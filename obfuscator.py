#!/usr/bin/python3

import builtins
from ast import (
    AST,
    AnnAssign,
    Assign,
    AsyncFunctionDef,
    Attribute,
    AugAssign,
    Call,
    ClassDef,
    Constant,
    ExceptHandler,
    Expr,
    FunctionDef,
    Global,
    Import,
    ImportFrom,
    JoinedStr,
    Load,
    Module,
)
from ast import Name as NameAst
from ast import NodeTransformer, Store
from ast import Tuple as TupleAst
from ast import alias, arg, parse, unparse
from base64 import b85encode, b85decode
from collections import UserDict
from dataclasses import dataclass
from logging import DEBUG, ERROR, debug, info
from random import choice, choices, randint
from re import finditer, sub
from string import ascii_letters, digits
from typing import Dict, Iterable, List, Tuple


@dataclass
class Name:
    """
    Dataclass with default name, obfuscation name, definition and namespace.

    name(str): default variable name
    obfuscation(str): variable name after obfuscation (a random name)
    is_attribute(bool): if True obfuscate this name as attribute
    namespace_name(str): the namespace (None or <class name> or
    <class name>.<function name>)
    """

    name: str
    obfuscation: str
    is_attribute: bool = False
    namespace_name: str = None


class NameMap(UserDict):
    def __init__(self):
        self.name_to_obfu = {}
        self.obfu_to_name = {}
        self.current_namespace = None
        self.names_size = 12

    def __getitem__(self, key):
        return self.name_to_obfu.__getitem__(key)

    def get_name(self, key, default=None):
        return self.name_to_obfu.get(key, default)

    def get_obfu(self, key, default=None):
        return self.obfu_to_name.get(key, default)

    # def get_reversed_names(self) -> Dict[str, Name]:
    #    rev = {}
    #    for name, data in self.values():
    #        if data

    def set_namespace_name(self, name: str) -> str:
        namespace = self.current_namespace
        if namespace is not None:
            self.current_namespace += "." + name
        else:
            self.current_namespace = name
        return namespace

    def generate_random_label(self) -> str:
        name = None
        while name is None or name in self.obfu_to_name.keys():
            first = choice("_" + ascii_letters)
            name = "".join(choices("_" + ascii_letters + digits, k=self.names_size - 1))
            name = first + name
        return name

    def get_random_name(self, first_name: str, is_attribute: bool = False) -> Name:
        """
        This function returns a random variable name.

        >>> Obfuscator("").get_random_name("test").name
        'test'
        >>>
        """
        name = self.get_name(first_name)
        if name is not None:
            if is_attribute:
                name.is_attribute = True
            return name

        name = Name(
            first_name,
            self.generate_random_label(),
            is_attribute,
            self.current_namespace,
        )

        return name

    def add_name(self, name: str, is_attribute: bool = False) -> Name:
        new_name = self.get_random_name(name, is_attribute)
        self.add(new_name)
        return new_name

    def add(self, name: Name):
        self.obfu_to_name[name.obfuscation] = name
        self.name_to_obfu[name.name] = name

    def add_names(self, names: Iterable[str] | str):
        if isinstance(names, str):
            names = (names,)
        for n in names:
            self.add_name(n)

    @staticmethod
    def obfuscate_names(names: List[str]) -> Dict[str, Name]:
        pass

    @staticmethod
    def add_builtins(names):
        names.add_names(set(dir() + dir(builtins)))


class Obfuscator(NodeTransformer):
    def __init__(self, source: str, encoding: str = "utf-8", names_size: int = 12):
        self.encoding = encoding
        self.names_size = names_size
        self.source = source
        self.in_format_string = False
        self._xor_password_key_length = 0
        self._xor_password_key = None

    def parse(self) -> AST:
        return parse(self.source)

    def visit_ExceptHandler(self, astcode: ExceptHandler) -> ExceptHandler:
        """
        This function obfuscates the except syntax.
        """

        astcode = self.generic_visit(astcode)
        if astcode.name:
            astcode.name = self.get_random_name(astcode.name).obfuscation
            info("Added random name in except syntax.")
        return astcode

    def visit_JoinedStr(self, astcode: JoinedStr) -> JoinedStr:
        """
        This function changes the visit_Constant's behaviour.
        """

        debug("Enter in joined str...")
        self.in_format_string = True
        astcode = self.generic_visit(astcode)
        self.in_format_string = False
        debug("Joined str end.")

    def encode_string(self, astcode: Constant):
        encoded = b85encode(astcode.value.encode())
        return parse(f"base64.b85decode({encoded})")

    def encrypt_obfuscate_string(self, astcode: Constant):
        debug(f"String obfuscation for {astcode.value!r}.")
        astcode.value = astcode.value.encode(self.encoding)
        astcode = self.generic_visit(astcode)
        return Call(
            func=Call(
                func=NameAst(id="getattr", ctx=Load()),
                args=[
                    Call(
                        func=NameAst(id="xor", ctx=Load()),
                        args=[Constant(value=self.xor(astcode.value), kind=None)],
                        keywords=[],
                    ),
                    Constant(value="decode", kind=None),
                ],
                keywords=[],
            ),
            args=[Constant(value="utf-8", kind=None)],
            keywords=[],
        )

    def visit_Constant(self, astcode: Constant) -> Call:
        """
        This function encrypts python constants data.
           (Level 2)

        - self.astcode is set to obfuscate ast code
        - returns the obfuscate ast code
        """

        is_str = isinstance(astcode.value, str)

        if is_str and not self.in_format_string:
            return self.encode_string(astcode)

        """
        elif isinstance(astcode.value, bytes) and not self.skip_bytes:
            debug(f"Bytes obfuscation for {astcode.value!r}.")
            astcode = self.generic_visit(astcode)
            return Call(
                func=NameAst(
                    id=self.default_names["xor"].obfuscation, ctx=Load()
                ),
                args=[Constant(value=self.xor(astcode.value))],
                keywords=[],
            )

        elif isinstance(astcode.value, int) and not self.in_format_string and not self.skip_ints:
            debug(f"Integer obfuscation for {astcode.value!r}")
            astcode = self.generic_visit(astcode)
            return Call(
                func=NameAst(
                    id=self.default_names["int"].obfuscation, ctx=Load()
                ),
                args=[
                    Constant(value=oct(astcode.value)),
                    Constant(value=8),
                ],
                keywords=[],
            )
        elif is_str:
            self.hard_coded_string.add((astcode.value, True))
        else:
            info(
                f"In format string {astcode.value!r} this "
                "constant type can't be obfuscated."
            )
            astcode = self.generic_visit(astcode)
        """

        return self.generic_visit(astcode)

    def xor(self, data: bytes) -> bytes:
        """
        This function encrypts data.

        data(bytes): data to encrypt
        return encrypted bytes
        """

        if self._xor_password_key is None:
            raise RuntimeError("To encrypt data the encryption key must be set.")

        cipher = [
            byte ^ self._xor_password_key[i % self._xor_password_key_length]
            for i, byte in enumerate(data)
        ]
        return bytes(cipher)

    @staticmethod
    def get_decrypt_function(xor_password: str, key_length: int) -> str:
        return (
            "xor=lambda bytes_:(bytes([x^"
            f"{xor_password}[i%{key_length}]"
            f" for i,x in enumerate(bytes_)]))\n"
        )

    @staticmethod
    def add_super_arguments(source: str) -> str:
        r"""
        This function adds super arguments because super
        can't defined it's arguments after obfuscation.

        >>> code = "class A:\n\tdef __init__(self):super().__init__()"
        >>> code, _ = Obfuscator("").add_super_arguments(code)
        >>> code
        'class A:\n\tdef __init__(self):super(self.__class__, self).__init__()'
        >>>
        """

        code = sub(
            r"\bsuper\b\(\)",
            "super(self.__class__, self)",
            source,
        )

        info("Super arguments is added.")
        return code

    @staticmethod
    def init_import(source: str) -> str:
        """
        This function adds an import function to try module
        'from <module>.<module> import <module>'.

        code(str) = None: if code this function use this code else
        it use self.code
        self.code is set to the new code
        Return the new code and AST.
        """

        return (
            "def myimport(module, element, *args, **kwargs):\n\ttry:return"
            " __import__(module+'.'+element, *args, **kwargs)\n\texcept"
            " ImportError:return __import__(module, *args, **kwargs)\n"
        ) + source

    @staticmethod
    def src_to_ast(self, source: str):
        self.source = source
        self.astcode = parse(source)
        return self.astcode

    @staticmethod
    def load_file(filename, encoding="utf-8"):
        src = ""
        with open(filename, "r", encoding=encoding) as f:
            src = f.read()
        return src

    def default_obfuscation(self) -> str:
        astcode = self.parse()
        astcode = self.visit(astcode)
        return unparse(astcode)


def main(*args):
    obfu = Obfuscator(Obfuscator.load_file("../simples/factorial_iter.py"))
    print(obfu.default_obfuscation())


if __name__ == "__main__":
    main()
