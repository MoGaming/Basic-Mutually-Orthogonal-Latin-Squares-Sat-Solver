import os
import subprocess
import sys
import time

if len(sys.argv) < 2:
    print("Usage: python3 generate.py <latin square order> [sat solver seed]")
    sys.exit(1)
elif int(sys.argv[1]) < 0:
    print("Error: <latin square order> must be a positive integer.")
    sys.exit(1)

script_dir = os.path.dirname(os.path.abspath(__file__))
parent_dir = os.path.dirname(script_dir)
input_path = os.path.join(script_dir, "input.cnf")
output_path = os.path.join(script_dir, "output.txt")
kissat_path = os.path.join(parent_dir, "kissat-rel-4.0.2", "build", "kissat") # update this to your sat solver's location 

start_time = time.time()
dimacs_elapsed = 0
kissat_elapsed = 0
verify_elapsed = 0

n = int(sys.argv[1]) # n > 0
if len(sys.argv) >= 3:
    seed = int(sys.argv[2]) # any integer 
else:
    seed = None
clauses = []
combinedLatinSquare = [] # combined latin square output, 2 latin square on top of each other 

def checkValid(square):
    n = len(square)
    if any(len(row) != n for row in square): # all rows are length n
        return False
    for row in square: # each row contains all symbols 0 to n-1 exactly once
        if sorted(row) != list(range(n)):
            return False
    for col_idx in range(n): # each column contains all symbols 0 to n-1 exactly once
        col = [square[row_idx][col_idx] for row_idx in range(n)]
        if sorted(col) != list(range(n)):
            return False
    return True

def checkOrthogonal(squares):
    square1 = squares[0:n]
    square2 = squares[n:n*2]
    exists = []
    for i in range(n):
        for j in range(n):
            pair = (square1[i][j], square2[i][j])
            if pair in exists:
                return False
            exists.append(pair)
    return True

def get1DIndex(l, r, c, s): # latin square, row, col, symbol, l = 0 or 1, 0 <= r, s, c <= n - 1
    return l * n**3 + r * n ** 2 + c * n + s + 1 # 1 to n^3

def get4DIndex(v): 
    v = v - 1  # Make it 0-based
    l = v // (n**3)
    rem = v % (n**3)
    r = rem // (n**2)
    rem = rem % (n**2)
    c = rem // n
    s = rem % n
    return l, r, c, s # l = 0 or 1, 0 <= r, c, s <= n - 1

for i in range(n): # fix first row and/or column of both squares, this speeds up finding a solution like in the case of MOLS of order 9 where it went from 32 min to 25 min
    clauses.append(str(get1DIndex(0, 0, i, i)))
    clauses.append(str(get1DIndex(1, 0, i, i)))
    clauses.append(str(get1DIndex(0, i, 0, i)))

for l in range(2): # maintain latin square clauses
    for x in range(n):
        for y in range(n): # create at least one value clause for row, col and symbol
            clause1 = "" # row
            clause2 = "" # col
            clause3 = "" # sym
            for z in range(n):
                clause1 = clause1 + str(get1DIndex(l, x,y,z)) + " "
                clause2 = clause2 + str(get1DIndex(l, x,z,y)) + " "
                clause3 = clause3 + str(get1DIndex(l, z,x,y)) + " "
                for w in range(z + 1, n): # at most one symbol (binary exclusions)
                    clauses.append("-" + str(get1DIndex(l, x,y,z)) + " -" + str(get1DIndex(l, x,y,w)))
                    clauses.append("-" + str(get1DIndex(l, x,z,y)) + " -" + str(get1DIndex(l, x,w,y)))
                    clauses.append("-" + str(get1DIndex(l, z,x,y)) + " -" + str(get1DIndex(l, w,x,y)))
            clauses.append(clause1)
            clauses.append(clause2)
            clauses.append(clause3)

for r1 in range(n): # maintain orthogonality clauses
    for c1 in range(n):
        for r2 in range(r1, n): # starting at r1 and c2 is to prevent duplicate iterations over the same positions
            c2Start = 0
            if r1 == r2:
                c2Start = c1 + 1 
            for c2 in range(c2Start, n):
                for s1 in range(n):
                    for s2 in range(n): # for each symbol pair (s1, s2), ensure it appears at most once across all (row, col) cells (e.g. position pairs)
                        clauses.append("-" + str(get1DIndex(0, r1, c1, s1)) + " -" + str(get1DIndex(1, r1, c1, s2)) + " -" + str(get1DIndex(0, r2, c2, s1)) + " -" + str(get1DIndex(1, r2, c2, s2)))

variableCount = get1DIndex(1, n - 1, n - 1, n - 1) 
clauseCount = len(clauses)

with open(input_path, "w") as f:
    f.write(f"p cnf {variableCount} {clauseCount}\n")
    for clause in clauses:
        f.write(f"{clause} 0\n") # repeat write is faster than string concat

dimacs_elapsed = round((time.time() - start_time) * 100)/100
print("Wrote DIMACS CNF file to:", input_path)  # might move this is a c++ or c implementation to speed it up
    
kissat_time = time.time() # wall time
with open(output_path, "w") as out_file:
    commands = [kissat_path, input_path]
    if seed != None: 
        commands.insert(1, "--seed=" + str(seed))
    subprocess.run(commands, stdout=out_file, stderr=subprocess.STDOUT)
kissat_elapsed = round((time.time() - kissat_time) * 100)/100

verify_time = time.time()
print("Wrote Kissat output to:", output_path)

with open(output_path, "r") as f:
    satisfiable = None
    for y in range(n*2):
        combinedLatinSquare.append([])
        for x in range(n):
            combinedLatinSquare[y].append(-1) # easily tells us if logic error occured by the existance of -1 symbol
    for line in f:
        if line.startswith("s "):
            if "UNSATISFIABLE" in line:
                satisfiable = "UNSAT"
            elif "SATISFIABLE" in line:
                satisfiable = "SAT"
        elif line.startswith("v "):
            values = line[2:].strip().split()
            for val in values:
                if val == '0': # end of variables
                    continue
                val = int(val)
                if val > 0:
                    l, r, c, s = get4DIndex(val)
                    combinedLatinSquare[r + l * n][c] = s

    print("Result:", satisfiable)
    if satisfiable == "SAT":
        for row in range(n*2):
            if row == n:
                print("")
            print(combinedLatinSquare[row])
        if checkValid(combinedLatinSquare[0 : n]) and checkValid(combinedLatinSquare[n : n*2]) and checkOrthogonal(combinedLatinSquare):
            print("\nValid solution produced by Kissat for latin squares of order", str(n) + ".")
        else:
            print("\nInvalid solution produced by Kissat")
verify_elapsed = round((time.time() - verify_time) * 100)/100
print("Total elapsed time of script:", round((time.time() - start_time) * 100)/100, "seconds")
print("     Dimacs elapsed time:", dimacs_elapsed, "seconds")
print("     Kissat elapsed time:", kissat_elapsed, "seconds")
print("     Verification elapsed time:", verify_elapsed, "seconds")
# cd /mnt/g/Code/sat\ solver\ stuff/mutually\ orthogonal\ latin\ squares