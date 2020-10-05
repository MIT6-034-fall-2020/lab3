# MIT 6.034 Lab 3: Constraint Satisfaction Problems
# Written by 6.034 staff

from constraint_api import *
from test_problems import get_pokemon_problem


#### Part 1: Warmup ############################################################

def has_empty_domains(csp) :
    """Returns True if the problem has one or more empty domains, otherwise False"""
    domains = csp.domains # gets domains
    for var in domains.keys(): # goes through variables
        if domains[var] == []: # sees if domain list is empty
            return True
    return False

def check_all_constraints(csp) :
    """Return False if the problem's assigned values violate some constraint,
    otherwise True"""
    """
    Gets all the assigned variables
    Iterates through them and checks each of their constraints
    Check based on the value 
    Only perform checks if other variable was assigned
    """

    assignments = csp.assignments # gets assigned variables-value dict
    assigned_vars = assignments.keys() # get the assigned variables
    for var in assigned_vars: # iterates per assigned variables
        constraints = csp.constraints_between(var, None) # gets constraints related to variable
        for constraint in constraints: # iterates through those constraints
            var2 = constraint.var2 # gets other variable 
            if var2 in assigned_vars: # check if other variable is assigned
                val1 = assignments[var] # gets val1 and val2
                val2 = assignments[var2]
                if not constraint.check(val1, val2): # checks for validity
                    return False
    return True



#### Part 2: Depth-First Constraint Solver #####################################

def solve_constraint_dfs(problem) :
    """
    Solves the problem using depth-first search.  Returns a tuple containing:
    1. the solution (a dictionary mapping variables to assigned values)
    2. the number of extensions made (the number of problems popped off the agenda).
    If no solution was found, return None as the first element of the tuple.
    """
    queue = [problem]
    extensions = 0
    while queue:
        curr = queue.pop(0)
        extensions += 1
        if not has_empty_domains(curr):
            if check_all_constraints(curr):
                if curr.unassigned_vars:
                    var = curr.pop_next_unassigned_var()
                    domains = curr.get_domain(var)
                    new_problems = []
                    for value in domains:
                        new_problem = curr.copy()
                        new_problem.set_assignment(var, value)
                        new_problems.append(new_problem)
                    queue = new_problems + queue
                else:
                    return (curr.assignments, extensions)

    return (None, extensions)


# QUESTION 1: How many extensions does it take to solve the Pokemon problem
#    with DFS?

# Hint: Use get_pokemon_problem() to get a new copy of the Pokemon problem
#    each time you want to solve it with a different search method.

print(solve_constraint_dfs(get_pokemon_problem()))
ANSWER_1 = 20


#### Part 3: Forward Checking ##################################################

def eliminate_from_neighbors(csp, var) :
    """
    Eliminates incompatible values from var's neighbors' domains, modifying
    the original csp.  Returns an alphabetically sorted list of the neighboring
    variables whose domains were reduced, with each variable appearing at most
    once.  If no domains were reduced, returns empty list.
    If a domain is reduced to size 0, quits immediately and returns None.
    """
    # see which of if w and v of W and V are incompatible
    def compare_val(V, W, v, w, csp=csp):
        constraints = csp.constraints_between(V, W)
        for constraint in constraints:
            if not constraint.check(v, w):
                return False
        return True

    reduced = []
    changed_vars = set()
    V_domain = csp.get_domain(var)
    neighbors = csp.get_neighbors(var) # get all neighbors
    for W in neighbors:
        W_domain = csp.get_domain(W)
        for w in W_domain:
            at_least_one = False
            for v in V_domain:
                if compare_val(var, W, v, w):
                    at_least_one = True
            if not at_least_one:
                reduced.append((W,w)) # add removed states and value
                changed_vars.add(W)

    for (var, val) in reduced:
        csp.eliminate(var, val)
        
    for var in changed_vars:
        if not csp.get_domain(var):
            return None

    return sorted(list(changed_vars))


# Because names give us power over things (you're free to use this alias)
forward_check = eliminate_from_neighbors

def solve_constraint_forward_checking(problem) :
    """
    Solves the problem using depth-first search with forward checking.
    Same return type as solve_constraint_dfs.
    """
    queue = [problem]
    extensions = 0
    while queue:
        curr = queue.pop(0)
        extensions += 1
        if not has_empty_domains(curr):
            if check_all_constraints(curr):
                if curr.unassigned_vars:
                    var = curr.pop_next_unassigned_var()
                    domains = curr.get_domain(var)
                    new_problems = []
                    for value in domains:
                        new_problem = curr.copy()
                        new_problem.set_assignment(var, value)
                        forward_check(new_problem, var)
                        new_problems.append(new_problem)
                    queue = new_problems + queue
                else:
                    return (curr.assignments, extensions)

    return (None, extensions)


# QUESTION 2: How many extensions does it take to solve the Pokemon problem
#    with DFS and forward checking?

print(solve_constraint_forward_checking(get_pokemon_problem()))
ANSWER_2 = 9


#### Part 4: Domain Reduction ##################################################

def domain_reduction(csp, queue=None) :
    """
    Uses constraints to reduce domains, propagating the domain reduction
    to all neighbors whose domains are reduced during the process.
    If queue is None, initializes propagation queue by adding all variables in
    their default order. 
    Returns a list of all variables that were dequeued, in the order they
    were removed from the queue.  Variables may appear in the list multiple times.
    If a domain is reduced to size 0, quits immediately and returns None.
    This function modifies the original csp.
    """
    dequeue = []
    # Only set queue if queue is None, not if empty
    if queue == None: 
        queue = csp.get_all_variables()
    while queue:
        var = queue.pop(0)
        dequeue.append(var)
        fc = forward_check(csp, var)
        if fc == None:
            return None
        for i in fc:
            if i not in queue:
                queue.append(i)

    return dequeue


# QUESTION 3: How many extensions does it take to solve the Pokemon problem
#    with DFS (no forward checking) if you do domain reduction before solving it?

q3 = get_pokemon_problem()
domain_reduction(q3)
print(solve_constraint_dfs(q3))

ANSWER_3 = 6


def solve_constraint_propagate_reduced_domains(problem) :
    """
    Solves the problem using depth-first search with forward checking and
    propagation through all reduced domains.  Same return type as
    solve_constraint_dfs.
    """
    queue = [problem]
    extensions = 0
    while queue:
        curr = queue.pop(0)
        extensions += 1
        if not has_empty_domains(curr):
            if check_all_constraints(curr):
                if curr.unassigned_vars:
                    var = curr.pop_next_unassigned_var()
                    domains = curr.get_domain(var)
                    new_problems = []
                    for value in domains:
                        new_problem = curr.copy()
                        new_problem.set_assignment(var, value)
                        domain_reduction(new_problem, [var])
                        new_problems.append(new_problem)
                    queue = new_problems + queue
                else:
                    return (curr.assignments, extensions)

    return (None, extensions)



# QUESTION 4: How many extensions does it take to solve the Pokemon problem
#    with forward checking and propagation through reduced domains?

print(solve_constraint_propagate_reduced_domains(get_pokemon_problem()))
ANSWER_4 = 7


#### Part 5A: Generic Domain Reduction #########################################

def propagate(enqueue_condition_fn, csp, queue=None) :
    """
    Uses constraints to reduce domains, modifying the original csp.
    Uses enqueue_condition_fn to determine whether to enqueue a variable whose
    domain has been reduced. Same return type as domain_reduction.
    """
    dequeue = []
    if queue == None: 
        queue = csp.get_all_variables()
    while queue:
        var = queue.pop(0)
        dequeue.append(var)
        fc = forward_check(csp, var)
        if fc == None:
            return None
        for i in fc:
            if i not in queue:
                if enqueue_condition_fn(csp, i):
                    queue.append(i)

    return dequeue

def condition_domain_reduction(csp, var) :
    """Returns True if var should be enqueued under the all-reduced-domains
    condition, otherwise False"""
    return True

def condition_singleton(csp, var) :
    """Returns True if var should be enqueued under the singleton-domains
    condition, otherwise False"""
    return (len(csp.get_domain(var)) == 1)

def condition_forward_checking(csp, var) :
    """Returns True if var should be enqueued under the forward-checking
    condition, otherwise False"""
    return False


#### Part 5B: Generic Constraint Solver ########################################

def solve_constraint_generic(problem, enqueue_condition=None) :
    """
    Solves the problem, calling propagate with the specified enqueue
    condition (a function). If enqueue_condition is None, uses DFS only.
    Same return type as solve_constraint_dfs.
    """
    queue = [problem]
    extensions = 0
    while queue:
        curr = queue.pop(0)
        extensions += 1
        if not has_empty_domains(curr):
            if check_all_constraints(curr):
                if curr.unassigned_vars:
                    var = curr.pop_next_unassigned_var()
                    domains = curr.get_domain(var)
                    new_problems = []
                    for value in domains:
                        new_problem = curr.copy()
                        new_problem.set_assignment(var, value)
                        if enqueue_condition != None:
                            propagate(enqueue_condition, new_problem, [var])
                        new_problems.append(new_problem)
                    queue = new_problems + queue
                else:
                    return (curr.assignments, extensions)

    return (None, extensions)

# QUESTION 5: How many extensions does it take to solve the Pokemon problem
#    with forward checking and propagation through singleton domains? (Don't
#    use domain reduction before solving it.)

print(solve_constraint_generic(get_pokemon_problem(), condition_singleton))
ANSWER_5 = 8


#### Part 6: Defining Custom Constraints #######################################

def constraint_adjacent(m, n) :
    """Returns True if m and n are adjacent, otherwise False.
    Assume m and n are ints."""
    return (abs(m-n) <= 1)

def constraint_not_adjacent(m, n) :
    """Returns True if m and n are NOT adjacent, otherwise False.
    Assume m and n are ints."""
    return (not constraint_adjacent(m, n))

def all_different(variables) :
    """Returns a list of constraints, with one difference constraint between
    each pair of variables."""
    raise NotImplementedError


#### SURVEY ####################################################################

NAME = None
COLLABORATORS = None
HOW_MANY_HOURS_THIS_LAB_TOOK = None
WHAT_I_FOUND_INTERESTING = None
WHAT_I_FOUND_BORING = None
SUGGESTIONS = None
