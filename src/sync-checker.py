#!/usr/bin/env python3

__version__ = "0.1.0"

import datetime
import os
import subprocess
import sys
import os.path
from pathlib import Path
from collections import defaultdict
from typing import Optional, Text, Iterator, Collection, TextIO, NamedTuple
import re
import fs
import humanize
from abc import ABC, abstractmethod
from fs import ResourceType
from fs.base import FS
from fs.info import Info
from fs.walk import Walker, Step
from progress.bar import PixelBar
from progress.counter import Counter
from pygtrie import StringTrie
import tomlkit
from tomlkit import TOMLDocument
import tomlkit.items
from tomlkit.items import _CustomDict


class FancyCounter(Counter):
    def __init__(self, message='', **kwargs):
        super().__init__(message, **kwargs)
        self.next(0)


class FancySizeCounter(FancyCounter):
    def update(self):
        message = self.message % self
        line = ''.join([message, humanize.naturalsize(self.index, gnu=True)])
        self.writeln(line)


class FancyBar(PixelBar):
    suffix = '%(percent).1f%% - %(eta)ds'

    def __init__(self, message='', **kwargs):
        super().__init__(message, **kwargs)
        self.next(0)

    def finish(self):
        self.suffix = 'Done'
        self.next(self.max - self.index)
        super().finish()


class FancyWalker(Walker):
    def __init__(self, hide_special=True):
        super().__init__()
        self.hide_special = hide_special

    def fancy_check_file(self, fs, path, info):
        return (not self.hide_special or info.type == ResourceType.file and not self.is_link(fs, path,
                                                                                             info)) and super().check_file(
            fs, info)

    def check_scan_dir(self, fs, path, info):
        return info.type == ResourceType.directory and not self.is_link(fs, path, info) and super().check_scan_dir(fs,
                                                                                                                   path,
                                                                                                                   info)

    def check_open_dir(self, fs, path, info):
        return (not self.hide_special or info.type == ResourceType.directory and not self.is_link(fs, path,
                                                                                                  info)) and super().check_scan_dir(
            fs, path, info)

    @staticmethod
    def load_link(fs: FS, root: str, info: Info) -> Info:
        if not info.has_namespace('link'):
            return fs.getinfo(info.make_path(root), namespaces='link')
        return info

    @staticmethod
    def is_link(fs, root, info):
        return FancyWalker.load_link(fs, root, info).is_link

    def walk(self, fs: FS, path: Text = "/", namespaces: Optional[Collection[Text]] = None) -> Iterator[Step]:
        updated_namespaces = ['details', 'link']
        if namespaces is not None:
            updated_namespaces.extend(namespaces)
        for step in super().walk(fs, path, updated_namespaces):
            file: Info
            if not self.hide_special:
                yield step
            else:
                # This is the only working method to skip links on ssh filesystem:
                #   resource type for links is file or directory even in local case,
                #   link namespace is not queries when walking through ssh filesystem.
                yield Step(step.path, step.dirs, [file for file in step.files if not self.is_link(fs, step.path, file)])


class DirStatIndexCollector(NamedTuple):
    empty_dir_index: TextIO
    link_index: TextIO
    special_index: TextIO


class CompareStat(NamedTuple):
    missing_file_count: int
    missing_subtrees: list[str]
    correspondence: dict[str, set[str]]


class DirStat(NamedTuple):
    file_count: int
    dir_count: int
    link_count: int
    special_count: int
    empty_dir_count: int
    size: int


class NamedFs(NamedTuple):
    fs: FS
    name: str
    url: str


class HashDict:
    checksum_to_path: defaultdict[str, set]

    def __init__(self, root_path):
        self.root_path = root_path
        self.checksum_to_path = defaultdict(set)
        self.path_to_checksum = StringTrie(separator="/")

    def put(self, path, checksum):
        self.checksum_to_path[checksum].add(path)
        self.path_to_checksum[path] = checksum

    def children(self, path) -> list[str]:
        def direct_child(deep_child):
            while self.parent(deep_child) != path:
                if self.parent(deep_child) == '':
                    raise Exception()
                deep_child = self.parent(deep_child)
            return deep_child

        return list(
            set([direct_child(child_desc[0]) for child_desc in self.path_to_checksum.items(path, shallow=True)]))

    @staticmethod
    def parent(path):
        result = fs.path.dirname(path)
        if result == "/":
            return ""
        else:
            return result

    def paths(self):
        result = set()
        for key in self.path_to_checksum.keys():
            ancestor = key
            while ancestor != self.root_path:
                if ancestor == '':
                    raise Exception()
                result.add(ancestor)
                ancestor = self.parent(ancestor)
        result.add(self.root_path)
        return sorted(result, key=len, reverse=True)


class ChecksumProvider(ABC):
    @abstractmethod
    def progress_max(self, stat: DirStat):
        pass

    @abstractmethod
    def progress_step(self, dir_fs: NamedFs, file_path: str):
        pass

    @abstractmethod
    def checksum(self, info: Info, file_path: str) -> str:
        pass


class Md5ChecksumProvider(ChecksumProvider):
    def __init__(self, host_fs: NamedFs):
        self.host_fs = host_fs

    def checksum(self, info: Info, file_path: str) -> str:
        full_path = os.path.normpath(os.path.join(self.host_fs.url, fs.path.relativefrom("/", file_path)))
        result = subprocess.run(["/usr/bin/env", "md5sum", full_path], stdout=subprocess.PIPE).stdout.decode()
        return result.split(" ")[0]

    def progress_max(self, stat: DirStat):
        return stat.size + 1024 * 512 * stat.file_count

    def progress_step(self, dir_fs: NamedFs, file_path: str):
        return dir_fs.fs.getsize(file_path) + 1024 * 512


class PipeMd5ChecksumProvider(ChecksumProvider):
    def __init__(self, host_fs: NamedFs):
        if host_fs.url.startswith("ssh://"):
            split: list[str] = re.split(r'(^[\w]+://|:[^:]*$)', host_fs.url)
            host = split[2]
            self.host_dir = split[3][1:]
        else:
            host = None
            self.host_dir = host_fs.url
        if host is None:
            self.process = subprocess.Popen(["xargs", "-L1", "md5sum"], stdin=subprocess.PIPE, stderr=subprocess.STDOUT,
                                            stdout=subprocess.PIPE, universal_newlines=True, bufsize=0)
        else:
            self.process = subprocess.Popen(["ssh", host, "xargs -L1 md5sum"], stdin=subprocess.PIPE,
                                            stderr=subprocess.STDOUT, stdout=subprocess.PIPE, universal_newlines=True,
                                            bufsize=0)

    def close(self):
        self.process.stdin.close()
        self.process.stdout.close()
        self.process.kill()

    def checksum(self, info: Info, file_path: str) -> str:
        full_path = os.path.normpath(os.path.join(self.host_dir, fs.path.relativefrom("/", file_path)))
        self.process.stdin.write(escape_for_xargs(full_path) + "\n")
        result = self.process.stdout.readline()
        return result.split(" ")[0]

    def progress_max(self, stat: DirStat):
        return stat.size + 1024 * 512 * stat.file_count

    def progress_step(self, dir_fs: NamedFs, file_path: str):
        return dir_fs.fs.getsize(file_path) + 1024 * 512


class NameSizeChecksumProvider(ChecksumProvider):
    def __init__(self, host_fs: NamedFs):
        pass

    def checksum(self, info: Info, file_path: str) -> str:
        size = info.size
        name = info.name
        name_filtered = re.sub(re.compile('[^\\w.\\-\\\\$]', re.U), '?', name)
        return name_filtered + "+" + str(size)

    def progress_max(self, stat: DirStat):
        return stat.file_count

    def progress_step(self, fs: NamedFs, file_path: str):
        return 1


def escape_for_xargs(path: str) -> str:
    return '"%s"' % re.sub('"', '"\\""', path)


def humanize_fs_path(path: str) -> str:
    if path == "" or path == "/":
        return "."
    return fs.path.relativefrom("/", path)


def count_stat(dir_fs: NamedFs, collector: DirStatIndexCollector) -> DirStat:
    bar = FancyCounter('Counting files in %s: ' % dir_fs.name)
    file_count = 0
    dir_count = 0
    links_count = 0
    special_count = 0
    empty_dir_count = 0
    dirs: list[Info]
    walker = FancyWalker(hide_special=False)
    for root, dirs, files in walker.walk(dir_fs.fs):
        for f in files:
            if f.type != ResourceType.file and f.type != ResourceType.symlink:
                special_count += 1
                print(humanize_fs_path(f.make_path(root)), file=collector.special_index)
            if walker.is_link(dir_fs.fs, root, f):
                links_count += 1
                target = walker.load_link(dir_fs.fs, root, f).get('link', 'target')
                print("%s -> %s" % (humanize_fs_path(f.make_path(root)), target), file=collector.link_index)
            else:
                file_count += 1
        for d in dirs:
            if d.type != ResourceType.directory and d.type != ResourceType.symlink:
                special_count += 1
                print(humanize_fs_path(d.make_path(root)), file=collector.special_index)
            if walker.is_link(dir_fs.fs, root, d):
                links_count += 1
                target = walker.load_link(dir_fs.fs, root, d).get('link', 'target')
                print("%s -> %s" % (humanize_fs_path(d.make_path(root)), target), file=collector.link_index)
            else:
                dir_count += 1
        if len(files) + len(dirs) == 0:
            empty_dir_count += 1
            print(humanize_fs_path(root), file=collector.empty_dir_index)
        bar.next(len(files) + len(dirs))
    bar.finish()
    bar = FancySizeCounter('Counting size of %s: ' % dir_fs.name)
    size = count_sizes(dir_fs.fs, bar)
    bar.finish()
    return DirStat(file_count=file_count,
                   size=size,
                   link_count=links_count,
                   dir_count=dir_count,
                   empty_dir_count=empty_dir_count,
                   special_count=special_count)


def read_config(config_path) -> TOMLDocument:
    return tomlkit.load(Path(config_path).open("r"))


def get_config_tables(config: _CustomDict, name: str = "", copy: bool = False) -> Iterator[tomlkit.items.AbstractTable]:
    current_table = {}
    child_tables = []
    for key, value in config.items():
        if isinstance(value, tomlkit.items.AbstractTable):
            if name == "":
                child_tables.extend(get_config_tables(value, "%s" % key))
            else:
                child_tables.extend(get_config_tables(value, "%s.%s" % (name, key)))
        else:
            current_table[key] = value
    if current_table != {}:
        if copy:
            current_table['name'] = name
            yield current_table
        else:
            config['name'] = name
            yield config
    yield from child_tables


def get_config_value(config_dict: dict, key: str):
    result = config_dict.get(key)
    if result is None:
        print("invalid config: %s is not specified" % key)
        exit(1)
    return result


def get_config_path_value(config_path, config_dict, key):
    return os.path.normpath(os.path.join(os.path.dirname(config_path), get_config_value(config_dict, key)))


def create_index_file(path, overwrite: bool):
    pure_path = Path(path)
    if not overwrite and pure_path.exists():
        print("could not create file %s: file already exists" % path)
        exit(1)
    return pure_path.open("w+")


def count_sizes(dir_fs, progress_bar):
    result = 0
    for root, dirs, files in FancyWalker().walk(dir_fs):
        for file in files:
            size = dir_fs.getsize(file.make_path(root))
            progress_bar.next(size)
            result += size
    return result


def create_index(index_file: TextIO, dir_fs: NamedFs, dir_stat: DirStat,
                 checksum_provider: ChecksumProvider) -> HashDict:
    bar = FancyBar('Building index for %s' % dir_fs.name, max=checksum_provider.progress_max(dir_stat))
    index_dict = HashDict("")
    for step in FancyWalker().walk(dir_fs.fs):
        file: Info
        for file in step.files:
            file_path = file.make_path(step.path)
            checksum = checksum_provider.checksum(file, file_path)
            index_dict.put(file_path, checksum)
            print("%s %s" % (checksum, humanize_fs_path(file_path)), file=index_file)
            bar.next(checksum_provider.progress_step(dir_fs, file_path))
    index_file.close()
    bar.finish()
    return index_dict


def compare_trees(all_tree_paths: list[str],
                  source_index: HashDict,
                  target_index: HashDict) -> CompareStat:
    missing: list[str] = []
    missing_file_count = 0
    correspondence: dict[str, set[str]] = {}
    bar = FancyBar('Comparing directory trees', max=2 * len(all_tree_paths))
    for source_file in all_tree_paths:
        checksum = source_index.path_to_checksum.get(source_file)
        if checksum is None:
            source_children = source_index.children(source_file)
            if all(elem in missing for elem in source_children):
                for elem in source_children:
                    missing.remove(elem)
                missing.append(source_file)
            if all(elem in correspondence for elem in source_children):
                target_children_parents: Optional[set[str]] = None
                for source_child in source_children:
                    target_child_parents = set(
                        target_index.parent(target_child) for target_child in correspondence[source_child])
                    if target_children_parents is None:
                        target_children_parents = target_child_parents
                    else:
                        target_children_parents = target_children_parents.intersection(target_child_parents)
                if len(set(target_children_parents)) >= 1:
                    for elem in source_children:
                        correspondence.pop(elem)
                    correspondence[source_file] = target_children_parents
            bar.next(len(source_children) + 1)
        else:
            target_file: Optional[set] = target_index.checksum_to_path.get(checksum)
            if target_file is None:
                missing_file_count += 1
                missing.append(source_file)
            else:
                correspondence[source_file] = target_file
            bar.next(1)
    bar.finish()
    return CompareStat(missing_file_count=missing_file_count,
                       missing_subtrees=missing,
                       correspondence=correspondence)


def do_work(config_table: dict, output_table: tomlkit.items.AbstractTable):
    name: str = get_config_value(config_table, 'name')
    print("")
    print("==============================")
    print("")
    print("Starting section %s" % ("<root>" if name == "" else name))
    table_index_path = os.path.join("index", name.replace(".", "/"))
    source_path = get_config_value(config_table, 'source')
    target_path = get_config_value(config_table, 'target')
    overwrite_index = get_config_value(config_table, 'overwrite-index')
    checksum_method = get_config_value(config_table, 'checksum-method')
    if checksum_method == 'md5':
        checksum_provider = PipeMd5ChecksumProvider
    elif checksum_method == 'name-size':
        checksum_provider = NameSizeChecksumProvider
    else:
        print("unsupported value: checksum-method = %s" % checksum_method)
        exit(1)
        raise Exception
    Path(table_index_path).mkdir(parents=True, exist_ok=True)

    source_fs = NamedFs(fs=fs.open_fs(source_path), name="source", url=source_path)
    target_fs = NamedFs(fs=fs.open_fs(target_path), name="target", url=target_path)

    source_empty_dirs_file = create_index_file(os.path.join(table_index_path, "source-empty-dirs"), overwrite_index)
    source_links_file = create_index_file(os.path.join(table_index_path, "source-links"), overwrite_index)
    source_special_file = create_index_file(os.path.join(table_index_path, "source-special"), overwrite_index)
    source_stat = count_stat(source_fs,
                             DirStatIndexCollector(empty_dir_index=source_empty_dirs_file, link_index=source_links_file,
                                                   special_index=source_special_file))
    source_empty_dirs_file.close()
    source_links_file.close()
    source_special_file.close()
    source_index_file = create_index_file(os.path.join(table_index_path, "source-index-%s" % checksum_method),
                                          overwrite_index)
    source_index = create_index(source_index_file, source_fs, source_stat, checksum_provider(source_fs))
    source_index_file.close()

    target_empty_dirs_file = create_index_file(os.path.join(table_index_path, "target-empty-dirs"), overwrite_index)
    target_links_file = create_index_file(os.path.join(table_index_path, "target-links"), overwrite_index)
    target_special_file = create_index_file(os.path.join(table_index_path, "target-special"), overwrite_index)
    target_stat = count_stat(target_fs,
                             DirStatIndexCollector(empty_dir_index=target_empty_dirs_file, link_index=target_links_file,
                                                   special_index=target_special_file))
    target_empty_dirs_file.close()
    target_links_file.close()
    target_special_file.close()
    target_index_file = create_index_file(os.path.join(table_index_path, "target-index-%s" % checksum_method),
                                          overwrite_index)
    target_index = create_index(target_index_file, target_fs, target_stat, checksum_provider(target_fs))
    target_index_file.close()

    output_table['source-file-count'] = source_stat.file_count
    output_table['target-file-count'] = target_stat.file_count
    output_table['source-dir-count'] = source_stat.dir_count
    output_table['target-dir-count'] = target_stat.dir_count
    output_table['source-empty-dir-count'] = source_stat.empty_dir_count
    output_table['target-empty-dir-count'] = source_stat.empty_dir_count
    output_table['source-special-file-count'] = source_stat.special_count
    output_table['target-special-file-count'] = target_stat.special_count
    output_table['source-link-count'] = source_stat.link_count
    output_table['target-link-count'] = target_stat.link_count
    output_table['source-link-count'].comment("Links were not compared, please check them manually,")
    output_table['target-link-count'].comment(
        "└─→links can be either local or external, please check that no data is overlooked.")
    output_table['source-distinct-file-count'] = len(source_index.checksum_to_path)
    output_table['target-distinct-file-count'] = len(target_index.checksum_to_path)
    output_table['source-size'] = source_stat.size
    output_table['target-size'] = target_stat.size
    source_fs.fs.close()
    target_fs.fs.close()
    all_tree_paths = source_index.paths()
    compare_stat = compare_trees(all_tree_paths, source_index, target_index)
    correspondence_file = create_index_file(os.path.join(table_index_path, "correspondence"), overwrite_index)
    missing_file = create_index_file(os.path.join(table_index_path, "missing"), overwrite_index)
    output_table['missing-subtrees'] = len(compare_stat.missing_subtrees)
    output_table['missing-files'] = compare_stat.missing_file_count
    output_table['script-version'] = __version__
    output_table['time'] = datetime.datetime.now()
    for m in compare_stat.missing_subtrees:
        print(humanize_fs_path(m), file=missing_file)
    for k in compare_stat.correspondence:
        for v in compare_stat.correspondence[k]:
            print("%s -> %s" % (humanize_fs_path(k), humanize_fs_path(v)), file=correspondence_file)


def main():
    if len(sys.argv) != 2:
        print("usage: %s config_path" % (os.path.basename(sys.argv[0])))
        exit(1)
    config_path = sys.argv[1]
    config_dir = os.path.dirname(config_path)
    os.chdir(config_dir)
    config_dict = read_config(os.path.basename(config_path))
    for table in get_config_tables(config_dict):
        do_work(table, table)
    output_file = create_index_file("config.log.toml", overwrite=True)
    tomlkit.dump(config_dict, output_file)


main()
