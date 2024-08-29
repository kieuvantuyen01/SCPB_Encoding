from typing import List
from pysat.formula import CNF
from pysat.solvers import Glucose3

id_variable = 0
sat_solver = Glucose3()

def pos_i(i, k, weight):
    if i == 0:
        return 0
    if i < k:
        sum_w = sum(weight[1:i+1])
        return min(k, sum_w)
    else:
        return k

def plus_clause(clause):
    sat_solver.add_clause(clause)
    print(clause)

def exactly_k(vars: List[int], weight: List[int], k):
    global id_variable
    n = len(vars) - 1
    
    # Create map_register to hold the auxiliary variables
    map_register = [[-1 for _ in range(k + 1)] for _ in range(n + 1)]

    for i in range(1, n + 1):
        n_bits = pos_i(i, k, weight)
        for j in range(1, n_bits + 1):
            id_variable += 1
            map_register[i][j] = id_variable

    print("Map register:")
    print(map_register)

    # (1) X_i -> R_i,j for j = 1 to w_i
    for i in range(1, n + 1):
        for j in range(1, weight[i] + 1):
            plus_clause([-vars[i], map_register[i][j]])

    # (2) R_{i-1,j} -> R_i,j for j = 1 to pos_{i-1}
    for i in range(2, n + 1):
        for j in range(1, pos_i(i - 1, k, weight) + 1):
            plus_clause([-map_register[i - 1][j], map_register[i][j]])

    # (3) X_i ^ R_{i-1,j} -> R_i,j+w_i for j = 1 to pos_{i-1}
    for i in range(2, n + 1):
        for j in range(1, pos_i(i - 1, k, weight) + 1):
            if j + weight[i] <= k:
                plus_clause([-vars[i], -map_register[i - 1][j], map_register[i][j + weight[i]]])

    # (4) ¬X_i ^ ¬R_{i-1,j} -> ¬R_i,j for j = 1 to pos_{i-1}
    for i in range(2, n + 1):
        for j in range(1, pos_i(i - 1, k, weight) + 1):
            plus_clause([vars[i], map_register[i - 1][j], -map_register[i][j]])

    # (5) ¬X_i -> ¬R_i,j for j = 1 + pos_{i-1} to pos_i
    for i in range(1, n + 1):
        for j in range(1 + pos_i(i - 1, k, weight), pos_i(i, k, weight) + 1):
            plus_clause([vars[i], -map_register[i][j]])

    # (6) ¬R_{i-1,j} -> ¬R_i,j+w_i for j = 1 to pos_{i-1}
    for i in range(2, n + 1):
        for j in range(1, pos_i(i - 1, k, weight) + 1):
            if j + weight[i] <= k:
                plus_clause([map_register[i - 1][j], -map_register[i][j + weight[i]]])

    # (7) R_{n-1,k} or (X_n ^ R_{n-1,k-w_n})
    plus_clause([map_register[n - 1][k], vars[n]])
    if k - weight[n] >= 0:
        plus_clause([map_register[n - 1][k - weight[n]], vars[n]])

    # (8) Encoding "At Most K" condition: 
    for i in range(2, n + 1):
        if k + 1 - weight[i] >= 0:
            plus_clause([-vars[i], -map_register[i - 1][k + 1 - weight[i]]])

def print_solution():
    print(f"Number of clauses: {sat_solver.nof_clauses()}")
    sat_status = sat_solver.solve()

    if not sat_status:
        print("No solutions found")
    else:
        solution = sat_solver.get_model()
        print("Solution found:", solution)

# Example usage
exactly_k([0, 1, 1, 1, 1], [0, 4, 4, 4, 4], 16)
print_solution()