import string
"""
| - logical disjunction
& - logical conjuction
^ - exclusive disjunction
~ - logical negation
> - logical consequence
= - if and only if
"""
def _and_(a, b):
    return a and b

def _or_(a, b):
    return a or b

def _xor_(a, b):
    return a != b

def _not_(a):
    return not a

def _iff_(a, b):
    return a == b

def _cons_(a, b):
    if a == True and b == False: return False;
    else: return True

LOG_FUN = {
    "&": _and_,
    ">": _cons_,
    "=": _iff_,
    "~": _not_,
    "|": _or_,
    "^": _xor_
}

OPS = "|&>~^="
VARS = string.ascii_lowercase
BIN = "01"

PRIO = {
    '=': 1,
    '>': 2,
    '|': 3,
    '&': 4,
    '^': 5,
    '~': 6,
}

#check if expression is correct
def isCorrect(logic_expr):
    logic_expr = "".join(logic_expr.split())
    prev = logic_expr[0]
    bracket_counter = 0
    for curr in logic_expr[1:]:
        if prev in OPS:
            if curr != '(' and curr not in VARS and curr not in BIN: return False

        if prev in VARS or prev in BIN:
            if curr != ')' and curr not in OPS: return False

        if prev == ')':
            if curr not in OPS and curr != ')':
                return False
            bracket_counter -= 1
            if bracket_counter < 0:
                return False

        if prev == '(':
            if curr not in VARS and curr not in BIN and curr != '(' and curr != '~':
                return False
            bracket_counter += 1

        prev = curr
    if prev == ')':
        bracket_counter -= 1

    if bracket_counter != 0:
            return False

    return True

#print list elements one by one in new lines
def print_list(my_list):
    print( '\n'.join([str(myelem) for myelem in my_list]))

#split variables and operators
def split_list(logic_expr):
    groups = set(list("".join(logic_expr.split())))
    ops = groups & set(VARS)
    varbs = groups & set(OPS)
    return sorted(ops), sorted(varbs)

PARR = {
    '&': 'r',
    '=': 'r',
    '>': 'r',
    '^': 'r',
    '|': 'r',
    '~': 'l'
}

def fill_zeros(binary_val, rest):
    to_fill = rest - len(binary_val)
    return "".join([str('0') for _ in range(to_fill)]) + binary_val

#concert expression to RPN
def logic_rpn(logic_expr):
    output = ""
    ops = []
    for curr in logic_expr:
        #if it is variable or value push element
        if curr in VARS or curr in BIN:
            output += curr
        #if it is a operator, we have to check priority
        if curr in OPS:
            if ops and ops[-1] != "(":
                curr_prio = PRIO[curr]
                parr1 = PARR[ops[-1]]
                prio1 = PRIO[ops[-1]]
                while (ops and ops[-1] != "(" and prio1 > curr_prio or (prio1 == curr_prio and parr1 == 'l')):
                    output += ops.pop()
                    if ops and ops[-1] != "(":
                        prio1 = PRIO[ops[-1]]
                        parr1 = PARR[ops[-1]]
            ops.append(curr)
        if curr == "(":
            ops.append(curr)
        if curr == ")":
            while ops[-1] != "(" :
                output += ops.pop()
            ops.pop()
    while ops:
        output += ops.pop()

    return output

#function to init/generate values before quine-mccluskey algorithm
def init_values(variables):
    var_len = len(variables)
    base_values = [bin(i)[2:] for i in range(2**var_len)]
    digit_amnt = len(base_values[-1])
    filled_values = map(lambda i: fill_zeros(i, digit_amnt), base_values)
    separated_values = list(map(list, filled_values))
    values = list(map(lambda v: dict(zip(variables, v)), separated_values))
    bool_set = [{'nvars': x, 'val': None} for x in values]
    return bool_set

#distill a needed values
def substitute_values(rpn_expr, info):
    valued_rpn_expr = ""
    for curr in rpn_expr:
        to_add = curr
        if curr in VARS:
            to_add = info['nvars'][curr]
        valued_rpn_expr += to_add
    return valued_rpn_expr

#string_to_bool
def s_to_b(s1):
    if s1 == "1": return True
    else: return False

#bool_to_string
def b_to_s(b1):
    if b1 == True: return "1"
    else: return "0"

#auxiliary function to ealuate
def evaluate(rpn_expr, info):
    rpn_expr_res = substitute_values(rpn_expr, info)
    stack = []

    for curr in rpn_expr_res:
        if curr == "~":
            v1  = s_to_b(stack.pop())
            res = b_to_s(LOG_FUN["~"](v1))
        elif curr in OPS and curr != "~":
            v2 = s_to_b(stack.pop())
            v1 = s_to_b(stack.pop())
            res = b_to_s(LOG_FUN[curr](v1, v2))
        else:
            res = curr
        stack.append(res)
    info['val'] = stack.pop()

#evaluate whole expression
def evaluate_whole(expr):
    rpn_expr = logic_rpn(expr)
    varbs, ops = split_list(rpn_expr)
    set = init_values(varbs)
    for info in set:
        evaluate(rpn_expr, info)
    return set

#Here start Quine-McCluskey algorithm
from functools import reduce
def convert_to_qm(info):
    qm_info = {}
    qm_info['nvars'] = info['nvars'].copy()
    qm_info['prop'] = {}

    bin_no = ""
    for var_value in info['nvars'].values():
        bin_no += var_value

    qm_info['prop']['no'] = [int(bin_no, 2)]
    qm_info['prop']['checked'] = False
    nvars = info['nvars'].values()
    qm_info['prop']['ones'] = reduce(lambda x, y: (x + 1) if y == '1' else x, nvars, 0)

    return qm_info


def get_positive_qm_set(set):
    positive_set = filter(lambda x: x['val'] == '1', set)
    positive_qm_set = [convert_to_qm(i) for i in positive_set]
    return positive_qm_set


def init_group(qm_set):
    var_count = len(qm_set[0]['nvars'])
    group = {i:[] for i in range(var_count + 1)}
    for qm_info in qm_set:
        group[qm_info['prop']['ones']].append(qm_info)

    return group


def compare_qm_set(qm_info1, qm_info2):
    diff_values = set(qm_info1['nvars'].items()) - set(qm_info2['nvars'].items())
    diff_key = list(diff_values)[0][0] if len(diff_values) == 1 else None
    return diff_key


def exist_in_group(new_no, group):
    group_nos = [qm_info['prop']['no'] for qm_info in group]
    return new_no in group_nos


def _next_group(prev_item):
    for ones in prev_item.keys():
        if prev_item[ones]:
            var_count = len(prev_item[ones][0]['nvars'])

    next_item = {i:[] for i in range(var_count + 1)}
    for ones, group in prev_item.items():
        for qm_info1 in group:
            next_ones = ones + 1
            if next_ones in prev_item.keys():
                next_group = prev_item[next_ones]
                for qm_info2 in next_group:
                    diff_key = compare_qm_set(qm_info1, qm_info2)
                    if diff_key:
                        new_ones = qm_info1['prop']['ones']
                        new_group = next_item[new_ones]
                        new_no = [no for no in qm_info1['prop']['no'] + qm_info2['prop']['no']]
                        new_no = sorted(new_no)
                        if not exist_in_group(new_no, new_group):
                            new_qm_info = {}
                            new_qm_info['nvars'] = dict(qm_info1['nvars'].copy())
                            new_qm_info['nvars'][diff_key] = '-'
                            new_qm_info['prop'] = {}
                            new_qm_info['prop']['no'] = new_no
                            new_qm_info['prop']['checked'] = False
                            new_qm_info['prop']['ones'] = qm_info1['prop']['ones']
                            new_group.append(new_qm_info)
                        qm_info1['prop']['checked'] = True
                        qm_info2['prop']['checked'] = True

    return next_item

#function groups sets
def group_clusters(bool_set):
    qm_set = get_positive_qm_set(bool_set)
    state = True
    items = [init_group(qm_set)]
    while state:
        items.append(_next_group(items[-1]))
        state = reduce(lambda x, y: bool(x or y), list(items[-1].values()), False)
    return items

#function searched unchecked positions
def filter_unchecked(items):
    unchecked_qm_set = []
    for item in items:
        for group in item.values():
            for qm_info in group:
                if qm_info['prop']['checked'] == False:
                    unchecked_qm_set.append(qm_info)
    return unchecked_qm_set

#function choose min searched set
from itertools import combinations, chain
def choose_min_set(unchecked_qm_set):
    positive_nos = set([])
    for qm_info in unchecked_qm_set:
        positive_nos = positive_nos | set(qm_info['prop']['no'])

    positive_nos = list(positive_nos)
    unchecked_nos = [qm_info['prop']['no'] for qm_info in unchecked_qm_set]
    for combination_length in range(len(unchecked_nos) + 1):
        qm_combinations = combinations(unchecked_nos, combination_length)
        for qm_combination in qm_combinations:
            unnested_qm_combination = list(chain.from_iterable(qm_combination))
            if set(unnested_qm_combination) == set(positive_nos):
                return [i for i in unchecked_qm_set if i['prop']['no'] in qm_combination]

#function to make output string
def qm_toString(chosen_qm_set):
    shortened_expr = ""
    chosen_var_values = [i['nvars'] for i in chosen_qm_set]
    for var_value in chosen_var_values:
        for var in var_value.keys():
            to_add = ""
            if var_value[var] == '0':
                to_add = '~' + var + '&'
            if var_value[var] == '1':
                to_add = var + '&'
            shortened_expr += to_add
        if shortened_expr[-1] == '&':
            shortened_expr = shortened_expr[:-1]
        shortened_expr += ' | '
    if shortened_expr[-3:] == ' | ':
            shortened_expr = shortened_expr[:-3]
    return shortened_expr

#function to shorten whole expression
def optimize(expr):
    if not isCorrect(expr):
        print("Incorrect input expression!");
        return

    varbs, ops = split_list(expr)
    bool_set = evaluate_whole(expr)
    items = group_clusters(bool_set)
    unchecked_qm_set = filter_unchecked(items)
    chosen_qm_set = choose_min_set(unchecked_qm_set)
    return qm_toString(chosen_qm_set)

#series of unit tests
import unittest

class TestCorrect(unittest.TestCase):
    def test_log_fun_not(self):
        self.assertEqual(LOG_FUN["~"](False), True)
    def test_log_fun_conj(self):
        self.assertEqual(LOG_FUN["&"](True, False), False)
    def test_log_fun_disj(self):
        self.assertEqual(LOG_FUN["|"](True, False), True)
    def test_log_fun_xor(self):
        self.assertEqual(LOG_FUN["^"](True, False), True)
    def test_log_fun_cons(self):
        self.assertEqual(LOG_FUN[">"](True, False), False)
    def test_log_fun_eq(self):
        self.assertEqual(LOG_FUN["="](True, False), False)
    def test_correct(self):
        self.assertEqual(isCorrect("((p | q) > (p & r))"), True)
    def test_token(self):
        self.assertEqual(split_list("((p | q) > (p & r))"), (['p', 'q', 'r'], ['&', '>', '|']))
    def test_rpn(self):
        self.assertEqual(logic_rpn("((p | q) > (p & r))"), "pq|pr&>")
    def test_generator(self):
        self.assertEqual(init_values(['p','q']),
        [{'nvars': {'q': '0', 'p': '0'}, 'val': None}, {'nvars': {'q': '1', 'p': '0'}, 'val': None},
        {'nvars': {'q': '0', 'p': '1'}, 'val': None}, {'nvars': {'q': '1', 'p': '1'}, 'val': None}])

def main():
    expr = input() #for example: "(((d | b & c)) & a)"
    print("Input expression is:\t\t"+expr)
    shortxpr = optimize(expr)
    print("Shortened input expression is:\t" + shortxpr)
    print("Let's test our program:")
    unittest.main()
