# to do 
# forward checking: set a value of a variable, check if all the constraints associated with that varaible are true e.g. set(1, 1) = "^" and check row_const1 and col_const1 for violations, if not do another assignemnt, if so remove a domain 
# don't implement, just call the right functions

'''
variables : grid spots so number of vars = nxn
domain : possible peice on the board
'''
# you cannot import csp and constrains, copy in section of code you need
import argparse
import sys
import heapq    ## added

class State:
    # This class is used to represent a state.
    # board : a list of lists that represents the 8*8 board
    def __init__(self, row_cnstr, col_cnstr, freq_type_ship, grid, board, consList, varList):

        self.row_cnstr = row_cnstr
        self.col_cnstr = col_cnstr
        self.freq_type_ship = freq_type_ship    # dictionary
        self.board = board
        self.grid = grid        # no padding
        self.consList = consList
        '''self.consListRow = consListRow
        self.consListCol = consListCol'''
        self.varList = varList

        self.width = len(board[0])
        self.height = len(board[0])
    
    def display(self):
        for i in self.board:
            for j in i:
                print(j, end="")
            print("")
        print("")


#implement various types of constraints
class Constraint:
    '''Base class for defining constraints. Each constraint can check if
       it has been satisfied, so each type of constraint must be a
       different class. For example a constraint of notEquals(V1,V2)
       must be a different class from a constraint of
       greaterThan(V1,V2), as they must implement different checks of
       satisfaction.

       However one can define a class of general table constraints, as
       below, that can capture many different constraints.

       On initialization the constraint's name can be given as well as
       the constraint's scope. IMPORTANT, the scope is ordered! E.g.,
       the constraint greaterThan(V1,V2) is not the same as the
       contraint greaterThan(V2,V1).
    '''
    def __init__(self, name, scope):
        '''create a constraint object, specify the constraint name (a
        string) and its scope (an ORDERED list of variable
        objects).'''
        self._scope = list(scope)
        self._name = "baseClass_" + name  #override in subconstraint types!

    def scope(self):
        return list(self._scope)

    def arity(self):
        return len(self._scope)

    def numUnassigned(self):
        i = 0
        for var in self._scope:
            if not var.isAssigned():
                i += 1
        return i

    def unAssignedVars(self):
        return [var for var in self.scope() if not var.isAssigned()]

    # def check(self): MASSIVE check if the n vars passed in have k vars which are ships (make sure thise spots are not = water)
    #     util.raiseNotDefined()

    def check(self, *vars, k, symbols):
        count = 0
        for var in vars:
            if var in symbols:
                count += 1
        return count == k

    def name(self):
        return self._name

    def __str__(self):
        return "Cnstr_{}({})".format(self.name(), map(lambda var: var.name(), self.scope()))

    def printConstraint(self):
        print("Cons: {} Vars = {}".format(
            self.name(), [v.name() for v in self.scope()]))


class Variable:
    '''Class for defining CSP variables.

      On initialization the variable object can be given a name and a
      list containing variable's domain of values. You can reset the
      variable's domain if you want to solve a similar problem where
      the domains have changed.

      To support CSP propagation, the class also maintains a current
      domain for the variable. Values pruned from the variable domain
      are removed from the current domain but not from the original
      domain. Values can be also restored.
    '''

    undoDict = dict()             #stores pruned values indexed by a
                                        #(variable,value) reason pair
    def __init__(self, name, domain):
        '''Create a variable object, specifying its name (a
        string) and domain of values.
        '''
        self._name = name                #text name for variable : coordinate
        self._dom = list(domain)         #Make a copy of passed domain : possible peices
        self._curdom = list(domain)      #using list
        self._value = None

    def __str__(self):
        return "Variable {}".format(self._name)

    def domain(self):
        '''return copy of variable domain'''
        return(list(self._dom))

    def domainSize(self):
        '''Return the size of the domain'''
        return(len(self.domain()))

    def resetDomain(self, newdomain):
        '''reset the domain of this variable'''
        self._dom = newdomain

    def getValue(self):
        return self._value

    def setValue(self, value):
        if value != None and not value in self._dom:
            print("Error: tried to assign value {} to variable {} that is not in {}'s domain".format(value,self._name,self._name))
        else:
            self._value = value    

    def unAssign(self):
        self.setValue(None)

    def isAssigned(self):
        return self.getValue() != None

    def name(self):
        return self._name

    def curDomain(self):
        '''return copy of variable current domain. But if variable is assigned
           return just its assigned value (this makes implementing hasSupport easier'''
        if self.isAssigned():
            return([self.getValue()])
        return(list(self._curdom))

    def curDomainSize(self):
        '''Return the size of the current domain'''
        if self.isAssigned():
            return(1)
        return(len(self._curdom))

    def inCurDomain(self, value):
        '''check if value is in current domain'''
        if self.isAssigned():
            return(value==self.getValue())
        return(value in self._curdom)

    def pruneValue(self, value, reasonVar, reasonVal):
        '''Remove value from current domain'''
        try:
            self._curdom.remove(value)
        except:
            print("Error: tried to prune value {} from variable {}'s domain, but value not present!".format(value, self._name))
        dkey = (reasonVar, reasonVal)
        if not dkey in Variable.undoDict:
            Variable.undoDict[dkey] = []
        Variable.undoDict[dkey].append((self, value))

    def restoreVal(self, value):
        self._curdom.append(value)

    def restoreCurDomain(self):
        self._curdom = self.domain()

    def reset(self):
        self.restoreCurDomain()
        self.unAssign()

    def dumpVar(self):
        print("Variable\"{}={}\": Dom = {}, CurDom = {}".format(self._name, self._value, self._dom, self._curdom))

    @staticmethod
    def clearUndoDict():
        undoDict = dict()

    @staticmethod
    def restoreValues(reasonVar, reasonVal):
        dkey = (reasonVar, reasonVal)
        if dkey in Variable.undoDict:
            for (var,val) in Variable.undoDict[dkey]:
                var.restoreVal(val)
            del Variable.undoDict[dkey]


def findvals(remainingVars, assignment, finalTestfn, partialTestfn=lambda x: True):
    '''Helper function for finding an assignment to the variables of a constraint
       that together with var=val satisfy the constraint. That is, this
       function looks for a supporing tuple.

       findvals uses recursion to build up a complete assignment, one value
       from every variable's current domain, along with var=val.

       It tries all ways of constructing such an assignment (using
       a recursive depth-first search).

       If partialTestfn is supplied, it will use this function to test
       all partial assignments---if the function returns False
       it will terminate trying to grow that assignment.

       It will test all full assignments to "allVars" using finalTestfn
       returning once it finds a full assignment that passes this test.

       returns True if it finds a suitable full assignment, False if none
       exist. (yes we are using an algorithm that is exactly like backtracking!)'''

    # print "==>findvars([",
    # for v in remainingVars: print v.name(), " ",
    # print "], [",
    # for x,y in assignment: print "({}={}) ".format(x.name(),y),
    # print ""

    #sort the variables call the internal version with the variables sorted
    remainingVars.sort(reverse=True, key=lambda v: v.curDomainSize())
    return findvals_(remainingVars, assignment, finalTestfn, partialTestfn)


def findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
    '''findvals_ internal function with remainingVars sorted by the size of
       their current domain'''
    if len(remainingVars) == 0:
        return finalTestfn(assignment)
    var = remainingVars.pop()
    for val in var.curDomain():
        assignment.append((var, val))
        if partialTestfn(assignment):
            if findvals_(remainingVars, assignment, finalTestfn, partialTestfn):
                return True
        assignment.pop()   #(var,val) didn't work since we didn't do the return
    remainingVars.append(var)
    return False


class NValuesConstraint(Constraint):
    '''NValues constraint over a set of variables.  Among the variables in
       the constraint's scope the number that have been assigned
       values in the set 'required_values' is in the range
       [lower_bound, upper_bound] (lower_bound <= #of variables
       assigned 'required_value' <= upper_bound)

       For example, if we have 4 variables V1, V2, V3, V4, each with
       domain [1, 2, 3, 4], then the call
       NValuesConstraint('test_nvalues', [V1, V2, V3, V4], [1,4], 2,
       3) will only be satisfied by assignments such that at least 2
       the V1, V2, V3, V4 are assigned the value 1 or 4, and at most 3
       of them have been assigned the value 1 or 4.

    '''

    def __init__(self, name, scope, required_values, lower_bound, upper_bound):
        Constraint.__init__(self,name, scope)
        self._name = "NValues_" + name
        self._required = required_values
        self._lb = int(lower_bound)
        self._ub = int(upper_bound)

    def check(self):
        assignments = []
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        rv_count = 0

        #print ("Checking {} with assignments = {}".format(self.name(), assignments))

        for v in assignments:
            if v in self._required:
                rv_count += 1

        #print ("rv_count = {} test = {}".format(rv_count, self._lb <= rv_count and self._ub >= rv_count))

        return self._lb <= rv_count and self._ub >= rv_count

    def hasSupport(self, var, val):
        '''check if var=val has an extension to an assignment of the
           other variable in the constraint that satisfies the constraint

           HINT: check the implementation of AllDiffConstraint.hasSupport
                 a similar approach is applicable here (but of course
                 there are other ways as well)
        '''
        if var not in self.scope():
            return True   #var=val has support on any constraint it does not participate in

        #define the test functions for findvals
        def valsOK(l):
            '''tests a list of assignments which are pairs (var,val)
               to see if they can satisfy this sum constraint'''
            rv_count = 0
            vals = [val for (var, val) in l]
            for v in vals:
                if v in self._required:
                    rv_count += 1
            least = rv_count + self.arity() - len(vals)
            most =  rv_count
            return self._lb <= least and self._ub >= most
        varsToAssign = self.scope()
        varsToAssign.remove(var)
        x = findvals(varsToAssign, [(var, val)], valsOK, valsOK)
        return x


class IfAllThenOneConstraint(Constraint):
    '''if each variable in left_side equals each value in left_values 
    then one of the variables in right side has to equal one of the values in right_values. 
    hasSupport tested only, check() untested.'''
    # left_side is the curr val and left_val is what the value should be
    def __init__(self, name, left_side, left_values, right_side, right_values):
        
        Constraint.__init__(self,name, left_side+[right_side])
        
        self._name = "IfAllThenOne_" + name
        self._ls = left_side
        self._rs = right_side
        self._lv = left_values
        self._rv = right_values

    def check(self):
        assignments = []
        
        for v in self.scope():
            if v.isAssigned():
                assignments.append(v.getValue())
            else:
                return True
        
        '''for i in range(len(self._ls)):
            # if it doesn't satisfy criteria don't apply it
            if self._ls[i] != self._lv:
                return True     # return true so it doesn't apply it
        
        if self._rs == self._rv:
            return True'''
        '''print(self._ls.getValue(), self._lv)
        input()'''
        '''if self._ls.getValue() not in self._lv:
            return True'''
        
        for i in range(len(self._ls)):
            if self._ls[i].getValue() != self._lv[i]:
                return True

        if self._rs.getValue() in self._rv:
            return True
        
        return False
        


#object for holding a constraint problem
class CSP:
    '''CSP class groups together a set of variables and a set of
       constraints to form a CSP problem. Provides a usesful place
       to put some other functions that depend on which variables
       and constraints are active'''

    def __init__(self, name, variables, constraints, vargrid):
        '''create a CSP problem object passing it a name, a list of
           variable objects, and a list of constraint objects'''
        self._name = name
        self._variables = variables
        self._constraints = constraints
        self.vargrid = vargrid

        #some sanity checks
        varsInCnst = set()
        for c in constraints:
            varsInCnst = varsInCnst.union(c.scope())
        for v in variables:
            if v not in varsInCnst:
                print("Warning: variable {} is not in any constraint of the CSP {}".format(v.name(), self.name()))
        for v in varsInCnst:
            if v not in variables:
                #print(f'v is {v}')
                print("Error: variable {} appears in constraint but specified as one of the variables of the CSP {}".format(v.name(), self.name()))

        self.constraints_of = [[] for i in range(len(variables))]
        for c in constraints:
            for v in c.scope():
                i = variables.index(v)
                self.constraints_of[i].append(c)

    def print_board(self):
        for i in range(len(self.vargrid)):
            row = ''
            for j in range(len(self.vargrid[i])):
                if self.vargrid[i][j].getValue():
                    row += self.vargrid[i][j].getValue()
                else:
                    row += '0'
            print(row)
        #print('-------------------------')
        

    def name(self):
        return self._name

    def variables(self):
        return list(self._variables)

    def constraints(self):
        return list(self._constraints)

    def constraintsOf(self, var):
        '''return constraints with var in their scope'''
        try:
            i = self.variables().index(var)
            return list(self.constraints_of[i])
        except:
            print("Error: tried to find constraint of variable {} that isn't in this CSP {}".format(var, self.name()))

    def unAssignAllVars(self):
        '''unassign all variables'''
        for v in self.variables():
            v.unAssign()

    def check(self, solutions):
        '''each solution is a list of (var, value) pairs. Check to see
           if these satisfy all the constraints. Return list of
           erroneous solutions'''

        #save values to restore later
        current_values = [(var, var.getValue()) for var in self.variables()]
        errs = []

        for s in solutions:
            s_vars = [var for (var, val) in s]

            if len(s_vars) != len(self.variables()):
                errs.append([s, "Solution has incorrect number of variables in it"])
                continue

            if len(set(s_vars)) != len(self.variables()):
                errs.append([s, "Solution has duplicate variable assignments"])
                continue

            if set(s_vars) != set(self.variables()):
                errs.append([s, "Solution has incorrect variable in it"])
                continue

            for (var, val) in s:
                var.setValue(val)

            for c in self.constraints():
                if not c.check():
                    errs.append([s, "Solution does not satisfy constraint {}".format(c.name())])
                    break

        for (var, val) in current_values:
            var.setValue(val)

        return errs
    
    def __str__(self):
        return "CSP {}".format(self.name())


def ship_constraints(csp, curr_type_ship):
    freq_type_ship = {'submarines': 0, 'destroyers': 0, 'cruisers': 0, 'battleships': 0}
    visited = set()

    for i in range(len(csp.vargrid)):
        for j in range(len(csp.vargrid[i])):
            if (i, j) in visited:
                continue

            count = 0
            value = csp.vargrid[i][j].getValue()

            if value == 'S':
                freq_type_ship['submarines'] += 1
                continue
            elif value == '<':
                row, col = i, j
                count = 1
                while csp.vargrid[row][col].getValue() != '>':
                    visited.add((row, col))
                    col += 1
                    count += 1
            elif value == '^':
                row, col = i, j
                count = 1
                while csp.vargrid[row][col].getValue() != 'v':
                    visited.add((row, col))
                    row += 1
                    count += 1

            if count == 2:
                freq_type_ship['destroyers'] += 1
            elif count == 3:
                freq_type_ship['cruisers'] += 1
            elif count == 4:
                freq_type_ship['battleships'] += 1
            elif count > 5:
                return False

    return freq_type_ship == curr_type_ship


def curr_num_ships(csp, curr_type_ship):
    freq_type_ship = {'submarines': 0, 'destroyers': 0, 'cruisers': 0, 'battleships': 0}
    visited = set()

    #print(curr_type_ship)

    '''
    If you have 1 of length 4, 2 of length 3, 3 of length 2, and 4 of length 1, 
    you know you have to have 4 S's, 5 M's, 9 < or ^, and 9 > or v
    '''

    num_S = curr_type_ship['submarines']
    num_M = curr_type_ship['cruisers'] + curr_type_ship['battleships']*2
    num_up_right = curr_type_ship['destroyers'] + curr_type_ship['cruisers'] + curr_type_ship['battleships'] 
    num_down_left = num_up_right

    
    count_num_S = 0
    count_num_M = 0
    count_num_up_right = 0
    count_down_left = 0

    for i in range(len(csp.vargrid)):
        for j in range(len(csp.vargrid[i])):
            value = csp.vargrid[i][j].getValue()

            if value == 'S':
                count_num_S += 1
            elif value == 'M':
                count_num_M += 1
            elif value == '^' or value == ">": 
                count_num_up_right += 1
            elif value == "v" or value == "<":
                count_down_left += 1
    
    '''csp.print_board()
    print(num_S,num_M, num_up,  num_left)
    print(count_num_S,count_num_M, count_num_up, count_left)
    input()'''
    
    
    if num_S < count_num_S:
        '''print(count_num_S, "here")
        input()'''
        return True
    if num_M < count_num_M:
        '''print(count_num_M, "here")
        input()'''
        return True
    if num_up_right < count_num_up_right:
        '''print(count_num_up, "here")
        input()'''
        return True
    if num_down_left < count_down_left:
        '''print(count_num_down, "here")
        input()'''
        return True

    return False



# MRV for var selection from Randy's code
def extract(assignedVars):
    nxtvar = min(assignedVars, key=lambda v: v.curDomainSize())
    assignedVars.remove(nxtvar)
    return nxtvar

# LCV for val selection
def orderVal(var, csp):
    orderVals = []
    for val in var.curDomain():
        conflicts = 0
        for con in csp.constraintsOf(var):
            for otherVar in con.unAssignedVars():
                if otherVar.inCurDomain(val):
                    conflicts += 1
        orderVals.append((val, conflicts))
    heapq.heapify(orderVals)
    return [heapq.heappop(orderVals)[0] for _ in range(len(orderVals))]


def FCCheck(constraint, assignedVar, assignedVal):
    var = constraint.unAssignedVars()[0]    # prune domain of unassigned variable, .unassigned()[0] constraint class attribute is list len 1 and var is single unassigned var of constraint
    for val in var.curDomain():     
        var.setValue(val)       # trial set and assign constraints, .curDomain is in variable class
        if not constraint.check():      # check() can be used directly in backtracking search on constraints with no unassigned variables left
            var.pruneValue(val, assignedVar, assignedVal)       # method is variable class
        var.unAssign()     # this val doesn't work so unassign from variable 
    if var.curDomainSize() == 0:
        return "DWO"    # domain wipe out with no values left for var
    else:
        return "OK"
        

def FC(csp, assignedVars, found, freq_type_ship):
    if assignedVars == []:
        if ship_constraints(csp, freq_type_ship) == True:       # check ship const is true then change found to true
            found = True
        return found

    var = extract(assignedVars)     # using MRV

    for val in orderVal(var, csp):      # LCV orders the values
        var.setValue(val)
        noDwo = True
        for con in csp.constraintsOf(var):          # returns a list of all relevant constrants related to that var list(self.constraints_of[i])
            if con.numUnassigned() == 1:        # you only look at contrants that have one unassigned variable
                if FCCheck(con, var, val) == "DWO":     # prune future variables
                    noDwo = False
                    break

        if noDwo:
            # Before calling FC again recursively, do some more pruning right there.
            # global counts of pieces used
            if curr_num_ships(csp, freq_type_ship) == False:     # num ships is too much
                
                found = FC(csp, assignedVars, found, freq_type_ship)
                if found:
                    return found
            
        if found == False:      # found false so then backtrack
            var.restoreValues(var, val)
    if found == False:      # found false so then backtrack
        var.setValue(None)      # undo assgnment to var
        assignedVars.append(var)    # restore vars to unassigned variables
    return found

def preprocess(grid, row_cnstr, col_cnstr):
    row_length, col_length = len(grid), len(grid[0])

    # Set values based on row and column constraints
    for i in range(row_length):
        if row_cnstr[i] == '0':
            grid[i] = ['.' for _ in range(col_length)]

    for j in range(col_length):
        if col_cnstr[j] == '0':
            for i in range(row_length):
                grid[i][j] = '.'
    
    for i in range(row_length):
        if j in range(col_length):
            if grid[i][j] == 'S':
                if (i == 0 and j != 0):
                    grid[i][j - 1] = '.'
                    grid[i][j + 1] = '.'
                    grid[i + 1][j] = '.'
                elif ((i == row_length - 1) and j != 0):
                    grid[i][j - 1] = '.'
                    grid[i][j + 1] = '.'
                    grid[i - 1][j] = '.'
                elif (i != 0 and j == 0):
                    grid[i + 1][j] = '.'
                    grid[i][j + 1] = '.'
                    grid[i - 1][j] = '.' 
                elif (i != 0 and j == (col_length - 1)):
                    grid[i + 1][j] = '.'
                    grid[i][j - 1] = '.' 
                    grid[i - 1][j] = '.'  
                else:
                    grid[i + 1][j] = '.'
                    grid[i][j - 1] = '.'
                    grid[i][j + 1] = '.'
                    grid[i - 1][j] = '.'
    return grid

def read_from_file(filename):

    f = open(filename)
    lines = f.readlines()

    freq_type_ship = {}
    freq_type_ship['submarines'] = int([x for x in lines[2][0].rstrip()][0])
    freq_type_ship['destroyers'] = int([x for x in lines[2][1].rstrip()][0])
    freq_type_ship['cruisers'] = int([x for x in lines[2][2].rstrip()][0])
    freq_type_ship['battleships'] = int([x for x in lines[2][3].rstrip()][0])
    grid = [[str(x) for x in l.rstrip()] for l in lines[3:]]
    row_cnstr = [x for x in lines[0].rstrip()]
    col_cnstr = [x for x in lines[1].rstrip()]

    # defining all the constraints and variables using cell based defn on pg 27 of slide 1: 
    varList = []        # variables: values that need to be found
    varn = {}       # constraints for each of the respective variables in varList
    consList = []
    vargrid = []

    # preprocess as many grid spots
    grid = preprocess(grid, row_cnstr, col_cnstr)

    # create the variables
    for i in range(len(grid)):
        var_row = []
        for j in range(len(grid[i])):
            domain = ['S', '.', '<', '>', '^', 'v', 'M']
            if grid[i][j] != '0':
                v = Variable(str(i) + str(j), [grid[i][j]])     # ships already defined
            else:   
                if (i == 0 or i == len(grid) - 1) and (j == 0 or j == len(grid[i]) - 1):
                    domain.remove('M')
                if i == 0:
                    domain.remove('v')
                if i == len(grid) - 1:
                    domain.remove('^')
                if j == 0:
                    domain.remove('>')
                if j == len(grid[i]) - 1:
                    domain.remove('<')
                v = Variable(str(i) + str(j), domain)       # for ships with mutiple peices, create a constrain to ensure these peices have their accompanying pieces beside them
            varList.append(v)
            varn[str(i) + str(j)] = v
            var_row.append(v)
        vargrid.append(var_row)

    # define row and column constraints
    for i in range(len(grid)):
        rowi = []
        coli = []
        for j in range(len(grid[i])):
            rowi.append(varn[ str(i) + str(j)])
            coli.append(varn[ str(j) + str(i)])

        # creating constraints object which are gonna get called in checked or hassupport that might cause prunning
        consList.append(NValuesConstraint('row' + str(i), rowi, ['S', '<', '>', '^', 'v', 'M'], row_cnstr[i], row_cnstr[i]))   # col constraints
        consList.append(NValuesConstraint('col' + str(i), coli, ['S', '<', '>', '^', 'v', 'M'], col_cnstr[i], col_cnstr[i]))   # row consttaints

    # each grid variable and check the four corners and compare that with grid variable   
    for i in range(len(grid)):
        for j in range(len(grid[i])):
            # check diagnoals
            # name, variables of the constrant class (variable will be middle square + each of teh 4 corners): put one peice bc you want binary, you want all the ship peieces, either one is a ship peiece or none
            if (i < len(grid) - 1) and (j < len(grid[i]) - 1):
                consList.append(NValuesConstraint(str(i+1), [varn[str(i)+str(j)], varn[str(i+1)+str(j+1)]] , ['S', '<', '>', '^', 'v', 'M'], 0, 1))   # row consttaints
            if (i > 0) and (j > 0):
                consList.append(NValuesConstraint(str(i-1), [varn[str(i)+str(j)], varn[str(i-1)+str(j-1)]] , ['S', '<', '>', '^', 'v', 'M'], 0, 1))    # row consttaints
            if (i < len(grid) - 1) and (j > 0):
                consList.append(NValuesConstraint(str(i+1), [varn[str(i)+str(j)], varn[str(i+1)+str(j-1)]] , ['S', '<', '>', '^', 'v', 'M'], 0, 1))   # row consttaints
            if (i > 0) and (j < len(grid[i]) - 1):
                consList.append(NValuesConstraint(str(i+1), [varn[str(i)+str(j)], varn[str(i-1)+str(j+1)]] , ['S', '<', '>', '^', 'v', 'M'], 0, 1))    # row consttaints
    

    x = 0
    def num():
        nonlocal x
        x = x + 1
        return "name" + str(x)

    # ship constraints, come up with diff ship constraints on the board
    # don't do water constraints
    # 38
    # after creating constraints, run and check again

    # define variables# define row and column constraints

    for i in range(len(grid)):
        for j in range(len(grid[i])):
            # if top left corner
            if (i == 0) and (j == 0):
                # check right and below square
                # right
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['<'], varn[str(i) + str(j+1)], ['>', 'M']))
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['^'], varn[str(i) + str(j+1)], ['.']))     # if left = ^ then right = [.]
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i) + str(j+1)], ['.'])) 
                # below
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['<'], varn[str(i+1) + str(j)], ['.']))        # if left = < then right = [.]
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i+1) + str(j)], ['.']))
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['^'], varn[str(i+1) + str(j)], ['v','M']))
                
            # elif top right corner
            elif (i == 0) and (j == len(grid[i]) - 1):
                # check left and down square
                # left
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['>'], varn[str(i) + str(j-1)], ['<','M']))
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['^'], varn[str(i) + str(j-1)], ['.']))     # if left = < then right = [.]              
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i) + str(j-1)], ['.'])) 
                # down 
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['>'], varn[str(i+1) + str(j)], ['.'])) 
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['^'], varn[str(i+1) + str(j)], ['v','M']))        # if left = ^ then right = [M, v]              
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i+1) + str(j)], ['.']))        # if left = < then right = [.]
                
            # elif bottom right
            elif (i == len(grid) - 1) and (j == len(grid[i]) - 1):
                # check left and top
                # left
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['v'], varn[str(i) + str(j-1)], ['.'])) 
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i) + str(j-1)], ['.'])) 
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['>'], varn[str(i) + str(j-1)], ['<','M']))     # if right = > then left = [<, M]                
                # top
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['>'], varn[str(i-1) + str(j)], ['.']))     # if left = < then right = [.]
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['v'], varn[str(i-1) + str(j)], ['^','M'])) 
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i-1) + str(j)], ['.']))     # if left = M then right = [., ^, M]
                  
            # elif bottom left corner
            elif (i == len(grid) - 1 ) and (j == 0):
                # check right and top
                # right 
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['<'], varn[str(i) + str(j+1)], ['>','M']))     # if left = < then right = [M, >]
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['v'], varn[str(i) + str(j+1)], ['.']))     # if left = ^ then right = [.]
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i) + str(j+1)], ['.']))
                
                # top
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['<'], varn[str(i-1) + str(j)], ['.']))     # if left = < then right = [.]
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['v'], varn[str(i-1) + str(j)], ['^','M']))
                consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i-1) + str(j)], ['.']))     # if left = M then right = [., ^, M]
            
            else:
                # non M constraints
                if (i > 0):
                    # check top
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i-1) + str(j)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['<'], varn[str(i-1) + str(j)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['>'], varn[str(i-1) + str(j)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['^'], varn[str(i-1) + str(j)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['v'], varn[str(i-1) + str(j)], ['^','M']))
                if (i < len(grid)-1):
                    # check bottom
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i+1) + str(j)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['<'], varn[str(i+1) + str(j)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['>'], varn[str(i+1) + str(j)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['^'], varn[str(i+1) + str(j)], ['v','M']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['v'], varn[str(i+1) + str(j)], ['.']))
                if (j > 0):
                    # check left
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i) + str(j-1)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['<'], varn[str(i) + str(j-1)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['>'], varn[str(i) + str(j-1)], ['<','M']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['^'], varn[str(i) + str(j-1)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['v'], varn[str(i) + str(j-1)], ['.']))
                if (j < len(grid)-1):
                    # check right
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['S'], varn[str(i) + str(j+1)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['<'], varn[str(i) + str(j+1)], ['>','M']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['>'], varn[str(i) + str(j+1)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['^'], varn[str(i) + str(j+1)], ['.']))
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['v'], varn[str(i) + str(j+1)], ['.']))

                # M constraints
                # edges
                # top row
                if (i == 0):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['M'], varn[str(i+1) + str(j)], ['.']))
                #bottom row
                if (i == len(grid)-1):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['M'], varn[str(i-1) + str(j)], ['.']))
                # left column
                if (j == 0):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['M'], varn[str(i) + str(j+1)], ['.']))
                # right column
                if (j == len(grid)-1):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)]], ['M'], varn[str(i) + str(j-1)], ['.']))
                # water top
                if (i > 0 and j > 0):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)], varn[str(i-1) + str(j)]], ['M','.'], varn[str(i) + str(j-1)], ['<','M']))
                if (i > 0 and j < len(grid)-1):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)], varn[str(i-1) + str(j)]], ['M', '.'], varn[str(i) + str(j+1)], ['>','M']))
                # water bottom
                if (i < len(grid)-1 and j > 0):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)], varn[str(i+1) + str(j)]], ['M','.'], varn[str(i) + str(j-1)], ['<','M']))
                if (i < len(grid)-1 and j < len(grid)-1):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)], varn[str(i+1) + str(j)]], ['M', '.'], varn[str(i) + str(j+1)], ['>','M']))
                # water left
                if (i > 0 and j > 0):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)], varn[str(i) + str(j-1)]], ['M','.'], varn[str(i-1) + str(j)], ['^','M']))
                if (i < len(grid)-1 and j > 0):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)], varn[str(i) + str(j-1)]], ['M', '.'], varn[str(i+1) + str(j)], ['v','M']))
                # water right
                if (i > 0 and j < len(grid)-1):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)], varn[str(i) + str(j+1)]], ['M','.'], varn[str(i-1) + str(j)], ['^','M']))
                if (i < len(grid)-1 and j < len(grid)-1):
                    consList.append(IfAllThenOneConstraint(num(), [varn[str(i) + str(j)], varn[str(i) + str(j+1)]], ['M', '.'], varn[str(i+1) + str(j)], ['v','M'])) 


    # purely for visualization purposes
    board = [[0 for x in range(len(col_cnstr) + 1)] for y in range(len(col_cnstr) + 1)]
    k,l, print_col = 0, 0, True
    for i in range(len(grid)):
        for j in range(len(grid[i])):
            if i != 0:
                board[i][j] = row_cnstr[k]
                k += 1
                break
            elif (i == 0 and j != 0) and (print_col):
                board[i][j] = col_cnstr[l]
                l += 1
            else:
                board[i][j] = grid[i][j]
        print_col = False

                
    f.close()

    return row_cnstr, col_cnstr, freq_type_ship, grid, board, varList, consList, vargrid

if __name__ == '__main__':

    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--inputfile",
        type=str,
        required=True,
        help="The input file that contains the puzzles."
    )
    parser.add_argument(
        "--outputfile",
        type=str,
        required=True,
        help="The output file that contains the solution."
    )
    args = parser.parse_args()

    row_cnstr, col_cnstr, freq_type_ship, grid, board, varList, consList, vargrid = read_from_file(args.inputfile)

    # variable and constraints are made inisde the read_from_file function
    state = State(row_cnstr, col_cnstr, freq_type_ship, grid, board, consList, varList)
    state.display()     # display initial state


    #add all constraints, variables to csp and solve
    csp = CSP('battle', varList,  consList, vargrid)
    #print("main",ret)
    ret = csp.variables()
    solutions = FC(csp, ret, False, freq_type_ship)       # csp is the specific costrant varList is a list of objects of class Variable
    
    csp.print_board()


    #print(ship_constraints(csp,freq_type_ship))


    # output results here
    sys.stdout = open(args.outputfile, 'w')
    #sys.stdout = sys.__stdout__
    # added
    if sys.stdout == None:
        ch = "None"
        sys.stdout.write(ch)
    else:
        csp.print_board()

    sys.stdout.close()
