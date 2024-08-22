from typing import List
from pysat.formula import CNF
from pysat.solvers import Glucose3, Solver

id_variable = 0
sat_solver = Glucose3()


def pos_i(i, k, weight):
    if i == 0: return 0
    if i < k:
        sum = 0
        for j in range(1, i+1):
            sum += weight[j]
        return min(k, sum)
    else:
        return k
    
def sum_weight(i, weight):
    sum = 0
    for j in range(1, i+1): 
        sum += weight[j]
    return sum

def plus_clause(clause):
    sat_solver.add_clause(clause)
    print(clause)
       

def exactly_k(vars: List[int], weight: List[int], k):
    global id_variable
    n = len(vars) - 1
    
    map_register = [[-1 for j in range(0, k + 1)] for i in range(0,n)]

    for i in range(1, n):
        n_bits = pos_i(i, k , weight)
        print(n_bits)
        for j in range(1, n_bits+1):
            id_variable += 1
            map_register[i][j] = id_variable
    print(map_register)


    # (1)
    for i in range(1, n):
        for j in range(1, weight[i] + 1):
            plus_clause([-1 * vars[i], map_register[i][j]])

    # (2)
    for i in range(2, n):
        for j in range(1, pos_i(i-1, k, weight)+1):
            plus_clause([-1 * map_register[i - 1][j], map_register[i][j]])

    # (3)
    for i in range(2, n):
        for j in range(1, pos_i(i-1, k, weight)+1):
            if j + weight[i] > k: 
                continue
            plus_clause([-1 * vars[i], -1 * map_register[i - 1][j], map_register[i][j + weight[i]]])

    # (4)
    for i in range(2, n):
        for j in range(1, pos_i(i-1, k, weight)+1):
            plus_clause([vars[i], map_register[i - 1][j], -1 * map_register[i][j]])

    # (5)
    for i in range(1, n):
        for j in range(1 + pos_i(i-1, k, weight), pos_i(i, k, weight) + 1):
            plus_clause([vars[i], -1 * map_register[i][j]])

    # (6)
    for i in range(2, n):
        for j in range(1, pos_i(i-1, k, weight)+1):
            if j + weight[i] > k: 
                continue
            plus_clause([map_register[i - 1][j], -1 * map_register[i][j+weight[i]]])

    # (7)
    plus_clause([map_register[n - 1][k], vars[n]])
    plus_clause([map_register[n - 1][k], map_register[n - 1][k - weight[n]]])

    # (8)
    for i in range(2, n + 1):
        plus_clause([-1 * vars[i], -1 * map_register[i - 1][k + 1 - weight[i]]])

def print_solution():
    print(sat_solver.nof_clauses())
    sat_status = sat_solver.solve_limited(expect_interrupt = True)

    if sat_status is False:
        print("No solutions found")
    else:
        solution = sat_solver.get_model()
        print(solution)

exactly_k([0,1,1,1,1], [0,4,4,4,4], 16)
print_solution()