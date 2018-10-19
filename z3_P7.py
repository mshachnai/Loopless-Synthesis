# P7 - Isolate right-most 0-bit

import z3
#from z3 import * considered bad practice but defines namespace z3

# List of Variables
I = z3.BitVec('I', 8)
O = z3.BitVec('O',8)
Y1 = z3.BitVec('Y1',8)
Y2 = z3.BitVec('Y2',8)
Y3 = z3.BitVec('Y3',8)
X11 = z3.BitVec('X11',8)
X12 = z3.BitVec('X12',8)
X21 = z3.BitVec('X21',8)
X22 = z3.BitVec('X22',8)
X31 = z3.BitVec('X31',8)
X32 = z3.BitVec('X32',8)

# List of numbering for each variables
ly1 = z3.Int('ly1')
ly2 = z3.Int('ly2')
ly3 = z3.Int('ly3')

lx11 = z3.Int('lx11')
lx12 = z3.Int('lx12')
lx21 = z3.Int('lx21')
lx22 = z3.Int('lx22')
lx31 = z3.Int('lx31')
lx32 = z3.Int('lx32')

# List of components.
phi1 = (Y1 == ~X11)
phi2 = (Y2 == (X21 + 1))
phi3 = (Y3 == (X31 & X32))



# Write the spec
spec_list = []
for t in range(8) :
    input_extract = []
    for tp in range(t + 1) :
        if tp == t :
            input_extract.append(z3.Extract(tp, tp, I) == 0)
        else :
            input_extract.append(z3.Extract(tp, tp, I) == 1)

    input_component = z3.And(input_extract)

    output_component = (O == z3.BitVecVal(2**t, 8))
    spec_list.append(z3.Implies(input_component, output_component))

# The case when I = 0 then O should be 1.
spec_list.append(z3.Implies(I == z3.BitVecVal(0, 8), O == z3.BitVecVal(1, 8)))

spec = z3.And(spec_list)

# phi cons = line number of two different instructions cannot be the same
phicons = z3.And(ly1 !=ly2, ly2!=ly3, ly1!=ly3)

# We only have three instructions.
# Bound the line number of each instruction and operand.
phibound = z3.And(ly1 >=1 , ly1 <=3 ,
                ly2 >=1 , ly2 <= 3,
                ly3 >=1 , ly3 <= 3,
                lx11 >=0, lx11 <=3,
                lx12 >=0, lx12 <=3,
                lx21 >=0, lx21 <=3,
                lx22 >=0, lx22 <=3,
                lx31 >=0, lx31 <=3,
                lx32 >=0, lx32 <=3)

# The operands of an instruction should use variables from previous lines.
phidep = z3.And(lx11 < ly1 , lx12 < ly1 , lx21 < ly2, lx22 < ly2, lx31 < ly3, lx32 < ly3)

# Connection information:
# First, the simple ones: if lx == 0, then x gets info from I
#                         if ly == 3, then O is y
phiconn = z3.And(z3.Implies(lx11 == 0, X11 == I),
              z3.Implies(lx12 == 0, X12 == I),
              z3.Implies(lx21 == 0, X21 == I),
              z3.Implies(lx22 == 0, X22 == I),
              z3.Implies(lx31 == 0, X31 == I),
              z3.Implies(lx32 == 0, X32 == I),
              z3.Implies(ly1 == 3,Y1 == O),
              z3.Implies(ly2 == 3,Y2 == O),
              z3.Implies(ly3 == 3,Y3 == O))

lys = [ly1, ly2, ly3]
lxs = [lx11, lx12, lx21, lx22, lx31, lx32]
lToVDict = {
    ly1: Y1,
    ly2: Y2,
    ly3: Y3,
    lx11: X11,
    lx12: X12,
    lx21: X21,
    lx22: X22,
    lx31: X31,
    lx32: X32
}

for i in lys :
    for j in lxs:
        phiconn = z3.And(phiconn, z3.Implies(i==j, lToVDict[i] == lToVDict[j]))

phiwfp = z3.And(phicons, phidep, phibound)

insideForAll = z3.ForAll([I, O, X11, X12, X21, X22, X31, X32, Y1, Y2, Y3], z3.Implies(z3.And(phi1, phi2, phi3, phiconn), spec))
final_formula = z3.And(phiwfp, insideForAll)

s = z3.Solver()
s.add(final_formula)
print (s.check())
print (s.model())

