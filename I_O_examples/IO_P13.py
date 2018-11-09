# P13 - Sign function -- I/O examples

import z3

# List of Variables
I = z3.BitVec('I', 8)
O = z3.BitVec('O',8)
Y1 = z3.BitVec('Y1',8)
Y2 = z3.BitVec('Y2',8)
Y3 = z3.BitVec('Y3',8)
Y4 = z3.BitVec('Y4',8)
X11 = z3.BitVec('X11',8)
X21 = z3.BitVec('X21',8)
X31 = z3.BitVec('X31',8)
X41 = z3.BitVec('X41',8)
X42 = z3.BitVec('X42',8)

# List of numbering for each variables
ly1 = z3.Int('ly1')
ly2 = z3.Int('ly2')
ly3 = z3.Int('ly3')
ly4 = z3.Int('ly4')

lx11 = z3.Int('lx11')
lx21 = z3.Int('lx21')
lx31 = z3.Int('lx31')
lx41 = z3.Int('lx41')
lx42 = z3.Int('lx42')

# List of components. phi-lib
phi1 = (Y1 == X11 >> 31)
phi2 = (Y2 == -X21)
phi3 = (Y3 == (X31 >> 31) & 0x01)
phi4 = (Y4 == X41 | X42)

# Write the spec using I/O examples --- works best with I/O examples and FOL constraint
spec = z3.And(z3.Implies(I == 1, O == 1), 
        z3.Implies(I == -5, O == -1),
        z3.Implies(I == 0, O == 0),
        z3.Implies(I > 0, O == 1),
        z3.Implies(I == 0, O == 0), 
        z3.Implies(I < 0, O == -1)) 
        #z3.Implies(I == 4, O == 1), 
        #z3.Implies(I == 6, O == 1), 
        #z3.Implies(I == -1, O == -1), 
        #z3.Implies(I == -2, O == -1), 
        #z3.Implies(I == -3, O == -1)) 
              #z3.Implies(I == -3, O == -1)) 

# phi cons = line number of two different instructions cannot be the same
phicons = z3.And(ly1!=ly2, ly2!=ly3, ly1!=ly3, ly1!=ly4, ly4!=ly2, ly4!=ly3)

# We only have four instructions.
# Bound the line number of each instruction and operand.
phibound = z3.And(ly1 >=1 , ly1 <=4,
                ly2 >=1, ly2 <=4,
                ly3 >=1, ly3 <=4,
                ly4 >=1, ly4 <=4,
                lx11 >=0, lx11 <=4,
                lx21 >=0, lx21 <=4,
                lx31 >=0, lx31 <=4,
                lx41 >=0, lx41 <=4,
                lx42 >=0, lx42 <=4)

# The operands of an instruction should use variables from previous lines. acyclicity
phidep = z3.And(lx11 < ly1, lx21 < ly2, 
                lx31 < ly3,
                lx41 < ly4, lx42 < ly4)

# Connection information:
# First, the simple ones: if lx == 0, then x gets info from I
#                         if ly == 4, then O is y
phiconn = z3.And(z3.Implies(lx11 == 0, X11 == I),
              z3.Implies(lx21 == 0, X21 == I),
              z3.Implies(lx31 == 0, X31 == I),
              z3.Implies(lx41 == 0, X41 == I),
              z3.Implies(lx42 == 0, X42 == I),
              z3.Implies(ly1 == 4,Y1 == O),
              z3.Implies(ly2 == 4,Y2 == O),
              z3.Implies(ly3 == 4,Y3 == O),
              z3.Implies(ly4 == 4,Y4 == O))

lys = [ly1, ly2, ly3, ly4]
lxs = [lx11, lx21, lx31, lx41, lx42]
lToVDict = {
    ly1: Y1,
    ly2: Y2,
    ly3: Y3,
    ly4: Y4,
    lx11: X11,
    lx21: X21,
    lx31: X31,
    lx41: X41,
    lx42: X42
}

for i in lys :
    for j in lxs:
        phiconn = z3.And(phiconn, z3.Implies(i==j, lToVDict[i] == lToVDict[j]))

phiwfp = z3.And(phicons, phidep, phibound)

insideForAll = z3.ForAll([I, O, X11, X21, X31, X41, X42, Y1, Y2, Y3, Y4], z3.Implies(z3.And(phi1, phi2, phi3, phi4, phiconn), spec))
final_formula = z3.And(phiwfp, insideForAll)

s = z3.Solver()
s.add(final_formula)
print (s.check())
print (s.model())



