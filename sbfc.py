import argparse
import sys
from collections import defaultdict


class State:
    def __init__(self):
        self.array = [0]
        self.pos = 0

    def _extend(self, pos):
        if pos >= len(self.array):
            alloc = pos - len(self.array) + 1
            self.array.extend(0 for _ in range(alloc))

    def move(self, offset):
        self.pos += offset
        self._extend(self.pos)

    def read(self, offset):
        pos = self.pos + offset
        self._extend(pos)
        return self.array[pos]

    def write(self, offset, value):
        pos = self.pos + offset
        self._extend(pos)
        self.array[pos] = value % 256

    def input(self, offset):
        self.write(offset, ord(sys.stdin.read(1)))

    def output(self, offset):
        sys.stdout.write(chr(self.read(offset)))
        sys.stdout.flush()


class Program:
    def __init__(self, insns):
        self.insns = insns

    def __str__(self):
        return '({})'.format(', '.join(map(str, self.insns)))

    def __len__(self):
        return sum(map(len, self.insns))

    def eval(self, state):
        for insn in self.insns:
            insn.eval(state)


class Loop:
    def __init__(self, offset, insns):
        self.offset = offset
        self.insns = insns

    def __str__(self):
        return '(while p[{}] do {})'.format(
            self.offset,
            ', '.join(map(str, self.insns))
        )

    def __len__(self):
        return 1 + sum(map(len, self.insns))

    def add_offset(self, offset):
        self.offset += offset

    def eval(self, state):
        while state.read(self.offset) != 0:
            for insn in self.insns:
                insn.eval(state)


class Insn:
    def __len__(self):
        return 1


class Move(Insn):
    def __init__(self, value):
        self.value = value

    def __str__(self):
        return 'p += {}'.format(self.value)

    def add_offset(self, offset):
        pass

    def eval(self, state):
        state.move(self.value)


class Input(Insn):
    def __init__(self, offset):
        self.offset = offset

    def __str__(self):
        return 'p[{}] = read()'.format(self.offset)

    def add_offset(self, offset):
        self.offset += offset

    def eval(self, state):
        state.input(self.offset)


class Output(Insn):
    def __init__(self, offset):
        self.offset = offset

    def __str__(self):
        return 'write(p[{}])'.format(self.offset)

    def add_offset(self, offset):
        self.offset += offset

    def eval(self, state):
        state.output(self.offset)


class Set(Insn):
    def __init__(self, offset, expr):
        self.offset = offset
        self.expr = expr

    def __str__(self):
        return 'p[{}] = {}'.format(self.offset, self.expr)

    def add_offset(self, offset):
        self.offset += offset
        self.expr.add_offset(offset)

    def eval(self, state):
        state.write(self.offset, self.expr.eval(state))

    def reads(self):
        return self.expr.reads()

    def writes(self):
        return self.offset

    def updates(self):
        return self.expr.updates()

    def simple(self):
        return self.expr.simple()

    def inline(self, offset, expr):
        return Set(self.offset, self.expr.subst({offset: expr}))


def _update_num(d, k, n):
    if k not in d:
        d[k] = n
    else:
        d[k] += n
        if d[k] == 0:
            del d[k]


class Poly:
    def __init__(self, coeff):
        self.coeff = coeff

    def __str__(self):
        if not self.coeff:
            return '0'
        items = []
        for var, num in sorted(self.coeff.items()):
            fvar = ' * '.join(
                'p[{}]^{}'.format(v, p) if p != 1 else 'p[{}]'.format(v)
                for v, p in var
            )
            if fvar:
                if num == 1:
                    items.append(fvar)
                else:
                    items.append('{} * {}'.format(num, fvar))
            else:
                items.append(str(num))
        return ' + '.join(items)

    def eval(self, state):
        result = 0
        for var, num in self.coeff.items():
            item = num
            for v, p in var:
                item *= state.read(v) ** p
            result += item
        return result

    def __eq__(self, other):
        return self.__class__ is other.__class__ and self.coeff == other.coeff

    def __add__(self, other):
        coeff = dict(self.coeff)
        for var, num in other.coeff.items():
            _update_num(coeff, var, num)
        return Poly(coeff)

    def __sub__(self, other):
        coeff = dict(self.coeff)
        for var, num in other.coeff.items():
            _update_num(coeff, var, -num)
        return Poly(coeff)

    def __mul__(self, other):
        coeff = {}
        for svar, snum in self.coeff.items():
            for ovar, onum in other.coeff.items():
                num = snum * onum
                dvar = dict(svar)
                for v, p in ovar:
                    _update_num(dvar, v, p)
                var = tuple(sorted(dvar.items()))
                _update_num(coeff, var, num)
        return Poly(coeff)

    def __pow__(self, other):
        if not isinstance(other, int):
            return NotImplemented
        if other <= 0:
            raise ValueError(other)
        result = const(1)
        for _ in range(other):
            result *= self
        return result

    def add_offset(self, offset):
        coeff = {}
        for var, num in self.coeff.items():
            nvar = tuple((v + offset, p) for v, p in var)
            coeff[nvar] = num
        self.coeff = coeff

    def subst(self, exprs):
        poly = const(0)
        for var, num in self.coeff.items():
            item = const(num)
            for v, p in var:
                if v in exprs:
                    item *= exprs[v] ** p
                else:
                    item *= load(v) ** p
            poly += item
        return poly

    def reads(self):
        return {v for var in self.coeff for v, _ in var}

    def updates(self):
        candidates = set()
        seen = set()
        for var, num in self.coeff.items():
            if len(var) == 1 and num == 1:
                v, p = var[0]
                if p == 1 and v not in seen:
                    candidates.add(v)
                seen.add(v)
            else:
                for v, _ in var:
                    candidates.discard(v)
                    seen.add(v)
        return candidates

    def simple(self):
        offsets = {}
        for var, num in self.coeff.items():
            if len(var) == 1:
                v, p = var[0]
                offsets[v] = v not in offsets and p == 1
            else:
                for v, _ in var:
                    offsets[v] = False
        return {o for o, s in offsets.items() if s}


def const(value):
    if value == 0:
        return Poly({})
    return Poly({(): value})


def load(offset):
    return Poly({((offset, 1),): 1})


def parse(src):
    stack = []
    insns = []
    for insn in src:
        if insn == '+':
            insns.append(Set(0, load(0) + const(1)))
        elif insn == '-':
            insns.append(Set(0, load(0) + const(-1)))
        elif insn == '>':
            insns.append(Move(1))
        elif insn == '<':
            insns.append(Move(-1))
        elif insn == ',':
            insns.append(Input(0))
        elif insn == '.':
            insns.append(Output(0))
        elif insn == '[':
            stack.append(insns)
            insns = []
        elif insn == ']':
            loop = Loop(0, insns)
            insns = stack.pop()
            insns.append(loop)
    return Program(insns)


def delay_moves(insns, start=0):
    out = []
    offset = 0
    for insn in insns:
        if isinstance(insn, Move):
            offset += insn.value
        else:
            if isinstance(insn, Loop):
                insn.insns = delay_moves(insn.insns, start=start + offset)
            insn.add_offset(start + offset)
            out.append(insn)
    if offset:
        out.append(Move(offset))
    return out


def _dfs_order(graph, start, insns, users):
    stack = [(start, iter(graph[start]))]
    visited = set([start])
    out = []
    prev_write = None
    prev_users = None
    prev_expr = None

    while stack:
        node, childs = stack[-1]
        for child in childs:
            if child not in visited:
                visited.add(child)
                stack.append((child, iter(graph[child])))
                break
        else:
            if node != start:
                insn = insns[node]
                if prev_write in insn.simple() and prev_users == {node}:
                    insn = insn.inline(prev_write, prev_expr)
                    out.pop()
                out.append(insn)
                prev_write = insn.writes()
                prev_users = users[node]
                prev_expr = insn.expr
            stack.pop()
            continue

    return out


def _inline_sets(insns):
    tail = len(insns)
    graph = {i: defaultdict(lambda: 0) for i in range(len(insns) + 1)}
    users = defaultdict(set)
    # forward pass
    recent_def = {}
    for i, insn in enumerate(insns):
        weight = 0
        simple = insn.simple()
        for o in insn.reads():
            if o in recent_def:
                w, d = recent_def[o]
                if o in simple:
                    w += 1
                # Insn should be placed after all used definitons
                graph[i][d] += w
                users[d].add(i)
                weight += w
        writes = insn.writes()
        if writes in recent_def:
            _, d = recent_def[writes]
            # Writes to same address should be keeped in order
            graph[i][d] += 0
        recent_def[writes] = (weight, i)
    for o, (w, d) in recent_def.items():
        graph[tail][d] = w
        users[d].add(tail)
    # backward pass
    nearest_def = {}
    for i, insn in reversed(list(enumerate(insns))):
        for o in insn.reads():
            if o in nearest_def:
                if i not in graph[nearest_def[o]]:
                    graph[nearest_def[o]][i] = 0
        nearest_def[insn.writes()] = i
    graph = {
        s: [t for t, _ in sorted(ts.items(), key=lambda a: (a[1], a[0]))]
        for s, ts in graph.items()
    }
    return _dfs_order(graph, tail, insns, users)


def inline_expressions(insns):
    out = []
    run = []
    for insn in insns:
        if isinstance(insn, Set):
            run.append(insn)
        else:
            out.extend(_inline_sets(run))
            if isinstance(insn, Loop):
                insn.insns = inline_expressions(insn.insns)
            out.append(insn)
            run = []
    out.extend(_inline_sets(run))
    return out


def _is_zero(loop):
    if len(loop.insns) != 1:
        return False
    insn = loop.insns[0]
    if not isinstance(insn, Set):
        return False
    return insn.offset == loop.offset and \
        insn.expr == load(loop.offset) + const(-1)


def _is_muladd(loop):
    has_decrement = False
    mutated = set()
    for insn in loop.insns:
        if not isinstance(insn, Set) or insn.offset in mutated:
            return False
        mutated.add(insn.offset)
    for insn in loop.insns:
        splitted = insn.expr - load(insn.offset)
        if splitted.reads() & mutated:
            return False
        if insn.offset == loop.offset:
            if has_decrement or splitted != const(-1):
                return False
            has_decrement = True
    return has_decrement


def replace_simple_loops(insns):
    out = []
    for insn in insns:
        if isinstance(insn, Loop):
            insn.insns = replace_simple_loops(insn.insns)
            if _is_zero(insn):
                insn = Set(insn.offset, const(0))
            elif _is_muladd(insn):
                for i in insn.insns:
                    if i.offset != insn.offset:
                        expr = (
                            load(insn.offset) * (i.expr - load(i.offset)) +
                            load(i.offset)
                        )
                        out.append(Set(i.offset, expr))
                insn = Set(insn.offset, const(0))
        out.append(insn)
    return out


PASSES = {
    0: [],
    1: [
        delay_moves,
        inline_expressions,
    ],
    2: [
        delay_moves,
        inline_expressions,
        replace_simple_loops,
        inline_expressions,
    ],
    3: [
        delay_moves,
        inline_expressions,
        replace_simple_loops,
        inline_expressions,
        inline_expressions,
    ],
}


def eval_source(args):
    with open(args.path, 'r') as fp:
        program = parse(fp.read())

    for opt in PASSES[args.opt_level]:
        before = len(program)
        program.insns = opt(program.insns)
        if args.verbose:
            print("{}: {} -> {}".format(opt.__name__, before, len(program)))

    program.eval(State())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('path')
    parser.add_argument(
        '-O', '--opt-level', type=int, default=2,
        choices=list(PASSES),
    )
    parser.add_argument('-v', '--verbose', action='store_true')
    args = parser.parse_args()
    eval_source(args)


if __name__ == '__main__':
    main()
