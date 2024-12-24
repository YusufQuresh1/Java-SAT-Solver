// IN1002 Introduction to Algorithms
// Coursework 2022/2023
//
// Submission by
// MOHAMMED QURESHI
// mohammed.qureshi.3@city.ac.uk

import java.io.BufferedReader;
import java.io.InputStreamReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

public class Solver {

    private int [][] clauseDatabase = null;
    private int numberOfVariables = 0;


    /* You answers go below here */

    // Part A.1
    // Worst case complexity : O(v)
    // Best case complexity : O(1)
    public boolean checkClause(int[] assignment, int[] clause) {
        int maxVar = clause[0];
        for (int i=1; i < clause.length; i++) {
            if (Math.abs(clause[i]) > Math.abs(clause[i - 1])) {
                maxVar = Math.abs(clause[i]);
            }
        }
        if (assignment.length >= maxVar+1) {
            for (int j : clause) {
                if ((j > 0 && assignment[j] == 1) ||
                        (j < 0 && assignment[-j] == -1)) {
                    return true;
                }
            }
        }
        return false;
    }

    // Part A.2
    // Worst case complexity : O(cl)
    // Best case complexity : O(l)
    public boolean checkClauseDatabase(int[] assignment, int[][] clauseDatabase) {
        for (int[] clause : clauseDatabase) {
            if (!checkClause(assignment, clause)) {
                return false;
            }
        }
        return true;
    }

    // Part A.3
    // Worst case complexity : O(v)
    // Best case complexity : O(1)
    public int checkClausePartial(int[] partialAssignment, int[] clause) {
        if (checkClause(partialAssignment, clause)) {
            return 1;
        }
        int maxVar = clause[0];
        for (int i=1; i < clause.length; i++) {
            if (Math.abs(clause[i]) > Math.abs(clause[i - 1])) {
                maxVar = Math.abs(clause[i]);
            }
        }
        if (partialAssignment.length >= maxVar+1) {
            for (int j : clause) {
                if ((j > 0 && partialAssignment[j] == 0) ||
                        (j < 0 && partialAssignment[-j] == 0)) {
                    return 0;
                }
            }
        }
        return -1;
    }

    // Part A.4
    // Worst case complexity : O(v)
    // Best case complexity : O(1)
    public int findUnit(int[] partialAssignment, int[] clause) {
        boolean oneZero = false;
        int literal = 0;
        if (checkClausePartial(partialAssignment, clause) == 0) {
            for (int i = 1; i < partialAssignment.length; i++) {
                if (partialAssignment[i] == 0) {
                    if (!oneZero) {
                        literal = clause[i-1];
                        oneZero = true;
                    } else {
                        return 0;
                    }
                }
            }
        }
        return literal;
    }

    // Part B
    // I think this can solve 1,2,3

    public int[] checkSat(int[][] clauseDatabase) {
        int[] satAssignment = new int[numberOfVariables + 1];

        List<List<Integer>> clauseD = Arrays.stream(clauseDatabase)
                .map(row -> Arrays.stream(row).boxed().collect(Collectors.toList()))
                .collect(Collectors.toList());  //converts clause database to list

        boolean sat = DPLL(clauseD, satAssignment);


        if (clauseD.isEmpty()) {
            for (int i = 1; i < satAssignment.length; i++) {
                if (satAssignment[i] == 0) {    //Clause should already be satisfiable
                    satAssignment[i] = -1;      // Either -1 or 1 should work
                    if (!checkClauseDatabase(satAssignment, clauseDatabase)) {
                        satAssignment[i] = 1;
                    }
                }
            }
        }
        if (sat) {
            return satAssignment;
        }
        return null;
    }

    public boolean DPLL(List<List<Integer>> clauseD, int[] satAssignment) {
        List<List<Integer>> unitClauses = new ArrayList<>();
        List<List<Integer>> clausesToRemove = new ArrayList<>();
        List<Integer> literalsToRemove = new ArrayList<>();
        for (List<Integer> clause : clauseD) {
            if (clause.size() == 1) {   //if clause is a unit clause
                if (satAssignment[Math.abs(clause.get(0))] == 0) {    //if is unassigned
                    if (clause.get(0) > 0) {
                        satAssignment[clause.get(0)] = 1;
                    } else {
                        satAssignment[-clause.get(0)] = -1;
                    } unitClauses.add(clause);
                    for (List<Integer> i : unitClauses) {
                        for (List<Integer> j : clauseD) {
                            if (j.contains(i.get(0)) && !clausesToRemove.contains(j)) {
                                clausesToRemove.add(j);
                                literalsToRemove.add(-(i.get(0)));

                            }
                        }
                    }


                }
                else {
                    return false;
                }
            }
        }
        List<List<Integer>> backtrack = clauseD.stream()
                .map(ArrayList::new)
                .collect(Collectors.toList());
        clauseD.removeAll(unitClauses);
        clauseD.removeAll(clausesToRemove);
        removeLiterals(literalsToRemove, clauseD);



        List<Integer> pureLiterals = findPureLiterals(clauseD);

        if (!pureLiterals.isEmpty()) {
            removePureLiterals(clauseD, pureLiterals, satAssignment);

        }
        if (clauseD.isEmpty()){
            return true;
        }
        if (clauseD.contains(Collections.emptyList())) {
            return false;
         }
        List<Integer> literal1 = new ArrayList<>();
        List<Integer> literal2 = new ArrayList<>();

        List<List<Integer>> choice1 = clauseD.stream()
                .map(ArrayList::new)
                .collect(Collectors.toList());
        List<List<Integer>> choice2 = clauseD.stream()
                .map(ArrayList::new)
                .collect(Collectors.toList());

        choice1.add(literal1);
        backtrack.add(literal2);


        boolean isRemainingLiterals = false;

        for (List<Integer> clause : clauseD) {
            if (clause.size() == 1) {
                isRemainingLiterals = true;
                break;
            }
        }
        pureLiterals = findPureLiterals(clauseD);
        if (!pureLiterals.isEmpty()) {
            removePureLiterals(clauseD, pureLiterals, satAssignment);
        }

        if (isRemainingLiterals) {
            DPLL(clauseD, satAssignment);
        } else {
            // Choose literal
            int l = clauseD.get(0).get(0);

            // Branch on l
            List<List<Integer>> clauseD1 = clauseD.stream()
                    .map(ArrayList::new)
                    .collect(Collectors.toList());
            clauseD1.add(Collections.singletonList(l));
            boolean result1 = DPLL(clauseD1, satAssignment);
            if (result1) return true;

            // Branch on not(l)
            List<List<Integer>> clauseD2 = clauseD.stream()
                    .map(ArrayList::new)
                    .collect(Collectors.toList());
            clauseD2.add(Collections.singletonList(-l));
            boolean result2 = DPLL(clauseD2, satAssignment);
            if (result2) return true;
        }
        return false;
        // return DPLL(choice1, satAssignment) || return DPLL(choice1, satAssignment);
    }

    public void removeLiterals(List<Integer> literalsToRemove, List<List<Integer>> clauseD){
        for (List<Integer> clause : clauseD) {
            if (clause.size() > 1) {
                clause.removeAll(literalsToRemove);
            }
        }
    }

    public void unitPropagate(List<Integer> unitClause, List<List<Integer>> clauseD) {

        List<List<Integer>> clausesToRemove = new ArrayList<>();

        for (List<Integer> j : clauseD) {
            if (j.contains(unitClause.get(0)) && !clausesToRemove.contains(j)) {
                clausesToRemove.add(j);
            }
        }

        clauseD.removeAll(clausesToRemove);

    }


    public List<Integer> findPureLiterals(List<List<Integer>> clauseD) {

        Map<Integer, Integer> literalCount = new HashMap<>();

        for (List<Integer> clause : clauseD) {
            for (int literal : clause) {
                int count = literalCount.getOrDefault(literal, 0);
                literalCount.put(literal, count + 1);
            }
        }

        List<Integer> pureLiterals = new ArrayList<>();

        for (Map.Entry<Integer, Integer> entry : literalCount.entrySet()) {
            int literal = entry.getKey();
            int count = entry.getValue();
            if (count > 0 && !literalCount.containsKey(-literal)) {
                pureLiterals.add(literal);

            }
        }

        return (pureLiterals);
    }
    public void removePureLiterals(List<List<Integer>> clauseD, List<Integer> pureLiterals, int[] satAssignment) {
        List<List<Integer>> clausesToRemove = new ArrayList<>();
        List<Integer> literalsToRemove = new ArrayList<>();
        for (Integer i : pureLiterals){
            literalsToRemove.add(-i);
        }
        removeLiterals(literalsToRemove, clauseD);
        for (List<Integer> clause : clauseD) {
            for (int literal : clause) {
                if (pureLiterals.contains(literal)) {
                    if (literal > 0 && Objects.requireNonNull(satAssignment)[literal] == 0){
                        satAssignment[literal] = 1;
                    } else if (literal < 0 && Objects.requireNonNull(satAssignment)[-literal] == 0) {
                        satAssignment[-literal] = -1;
                    }
                    clausesToRemove.add(clause);
                }
            }
        }
        clauseD.removeAll(clausesToRemove);

        if(!findPureLiterals(clauseD).isEmpty() && satAssignment != null) {
            removePureLiterals(clauseD, findPureLiterals(clauseD), satAssignment);
        }

        //return satAssignment;
    }


    /*****************************************************************\
     *** DO NOT CHANGE! DO NOT CHANGE! DO NOT CHANGE! DO NOT CHANGE! ***
     *******************************************************************
     *********** Do not change anything below this comment! ************
     \*****************************************************************/

    public static void main(String[] args) {
        try {
            Solver mySolver = new Solver();

            System.out.println("Enter the file to check");

            InputStreamReader isr = new InputStreamReader(System.in);
            BufferedReader br = new BufferedReader(isr);
            String fileName = br.readLine();

            int returnValue = 0;

            Path file = Paths.get(fileName);
            BufferedReader reader = Files.newBufferedReader(file);
            returnValue = mySolver.runSatSolver(reader);

            return;

        } catch (Exception e) {
            System.err.println("Solver failed :-(");
            e.printStackTrace(System.err);
            return;

        }
    }

    public int runSatSolver(BufferedReader reader) throws Exception, IOException {

        // First load the problem in, this will initialise the clause
        // database and the number of variables.
        loadDimacs(reader);

        // Then we run the part B algorithm
        int [] assignment = checkSat(clauseDatabase);

        // Depending on the output do different checks
        if (assignment == null) {
            // No assignment to check, will have to trust the result
            // is correct...
            System.out.println("s UNSATISFIABLE");
            return 20;

        } else {
            // Cross check using the part A algorithm
            boolean checkResult = checkClauseDatabase(assignment, clauseDatabase);

            if (checkResult == false) {
                throw new Exception("The assignment returned by checkSat is not satisfiable according to checkClauseDatabase?");
            }

            System.out.println("s SATISFIABLE");

            // Check that it is a well structured assignment
            if (assignment.length != numberOfVariables + 1) {
                throw new Exception("Assignment should have one element per variable.");
            }
            if (assignment[0] != 0) {
                throw new Exception("The first element of an assignment must be zero.");
            }
            for (int i = 1; i <= numberOfVariables; ++i) {
                if (assignment[i] == 1 || assignment[i] == -1) {
                    System.out.println("v " + (i * assignment[i]));
                } else {
                    throw new Exception("assignment[" + i + "] should be 1 or -1, is " + assignment[i]);
                }
            }

            return 10;
        }
    }

    // This is a simple parser for DIMACS file format
    void loadDimacs(BufferedReader reader) throws Exception, IOException {
        int numberOfClauses = 0;

        // Find the header line
        do {
            String line = reader.readLine();

            if (line == null) {
                throw new Exception("Found end of file before a header?");
            } else if (line.startsWith("c")) {
                // Comment line, ignore
                continue;
            } else if (line.startsWith("p cnf ")) {
                // Found the header
                String counters = line.substring(6);
                int split = counters.indexOf(" ");
                numberOfVariables = Integer.parseInt(counters.substring(0,split));
                numberOfClauses = Integer.parseInt(counters.substring(split + 1));

                if (numberOfVariables <= 0) {
                    throw new Exception("Variables should be positive?");
                }
                if (numberOfClauses < 0) {
                    throw new Exception("A negative number of clauses?");
                }
                break;
            } else {
                throw new Exception("Unexpected line?");
            }
        } while (true);

        // Set up the clauseDatabase
        clauseDatabase = new int[numberOfClauses][];

        // Parse the clauses
        for (int i = 0; i < numberOfClauses; ++i) {
            String line = reader.readLine();

            if (line == null) {
                throw new Exception("Unexpected end of file before clauses have been parsed");
            } else if (line.startsWith("c")) {
                // Comment; skip
                --i;
                continue;
            } else {
                // Try to parse as a clause
                ArrayList<Integer> tmp = new ArrayList<Integer>();
                String working = line;

                do {
                    int split = working.indexOf(" ");

                    if (split == -1) {
                        // No space found so working should just be
                        // the final "0"
                        if (!working.equals("0")) {
                            throw new Exception("Unexpected end of clause string : \"" + working + "\"");
                        } else {
                            // Clause is correct and complete
                            break;
                        }
                    } else {
                        int var = Integer.parseInt(working.substring(0,split));

                        if (var == 0) {
                            throw new Exception("Unexpected 0 in the middle of a clause");
                        } else {
                            tmp.add(var);
                        }

                        working = working.substring(split + 1);
                    }
                } while (true);

                // Add to the clause database
                clauseDatabase[i] = new int[tmp.size()];
                for (int j = 0; j < tmp.size(); ++j) {
                    clauseDatabase[i][j] = tmp.get(j);
                }
            }
        }

        // All clauses loaded successfully!
        return;
    }

}
