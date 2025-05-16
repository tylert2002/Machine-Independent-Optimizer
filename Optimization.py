from collections import defaultdict

def getLineNumber(line_str):
    return int(line_str.replace('(', '').replace(')', ''))

def sanitizeInstruction(instruction):
    return instruction.replace("\n", "")

def getAllLeadersSorted(allInstructionLines):
   # Step 1: Get all leaders
    leaders = set([1])  # First instruction is a leader
    for idx, wholeLine in enumerate(allInstructionLines):
        line, instruction = wholeLine.split(" ", 1)  # Split into line number and instruction
        line = getLineNumber(line)
        instruction = sanitizeInstruction(instruction)
        # Targets of jumps
        if "goto" in instruction:
            target = int(instruction.split("(")[1].split(")")[0])
            leaders.add(target)
        # Instructions following jumps (next instruction after a jump or conditional)
        if "goto" in instruction or "if" in instruction:
            if idx + 1 < len(allInstructionLines):
                next_line, next_instruction = allInstructionLines[idx + 1].split(" ", 1)
                leaders.add(getLineNumber(next_line))
    return sorted(leaders)

def constructAllBasicBlocks(allInstructions, leaders):
    # Step 2: Construct basic blocks
    blocks = []
    current_block = []
    block_map = {}  # Map line number to block ID
    for wholeLine in allInstructions:
        line, instruction = wholeLine.split(" ", 1)
        line = getLineNumber(line)
        instruction = sanitizeInstruction(instruction)
        if line in leaders and current_block:  
            blocks.append((f"Basic Block {len(blocks) + 1}", current_block))
            current_block = []
        current_block.append((line, instruction))
        block_map[line] = len(blocks) + 1
    if current_block:  
        blocks.append((f"Basic Block {len(blocks) + 1}", current_block))
    return blocks, block_map

def constructCFG(blocks, block_map, allInstructions):
    # Step 3: Construct CFG
    successors = defaultdict(list)
    predecessors = defaultdict(list)
    for block_id, (block_name, block_instructions) in enumerate(blocks):
        last_instruction = block_instructions[-1][1]  # Last instruction in the block
        last_line = block_instructions[-1][0]  # Line number of the last instruction
        if "goto" in last_instruction and "if" not in last_instruction:
            # Unconditional jump
            target = int(last_instruction.split("(")[1].split(")")[0])
            target_block = block_map[target]
            successors[block_name].append(f"Basic Block {target_block}")
            predecessors[f"Basic Block {target_block}"].append(block_name)
        elif "if" in last_instruction:
            # Conditional jump: both target and fall-through
            target = int(last_instruction.split("(")[1].split(")")[0])
            target_block = block_map[target]
            successors[block_name].append(f"Basic Block {target_block}")
            predecessors[f"Basic Block {target_block}"].append(block_name)
            # Fall-through to next block
            if last_line != getLineNumber(allInstructions[-1].split(" ", 1)[0]):
                next_line = last_line + 1
                next_block = block_map[next_line]
                successors[block_name].append(f"Basic Block {next_block}")
                predecessors[f"Basic Block {next_block}"].append(block_name)
        elif last_instruction != "return":
            # Fall-through to next block
            if last_line != getLineNumber(allInstructions[-1].split(" ", 1)[0]):
                next_line = last_line + 1
                next_block = block_map[next_line]
                successors[block_name].append(f"Basic Block {next_block}")
                predecessors[f"Basic Block {next_block}"].append(block_name)
    return successors, predecessors

def reachingDefinitionsAnalysis(blocks, predecessors, output_file):
    # Step 4: Reaching Definition Analysis
    definitions = {}
    def_id = 1
    for block_name, instructions in blocks:
        for line, instruction in instructions:
            if "=" in instruction and "if" not in instruction and "goto" not in instruction and "return" not in instruction:
                variable = instruction.split("=")[0].strip()
                if "[" in variable:
                    variable = f"x[{variable.split('[')[1].split(']')[0]}]"
                definitions[f"d{def_id}"] = (variable, line, instruction)
                def_id += 1

    # Write definitions to file
    output_file.write("\nDefinitions:\n")
    print("\nDefinitions:")
    for def_key, (variable, line, instruction) in definitions.items():
        output_line = f"{def_key}: {variable} at line {line} ({instruction})\n"
        output_file.write(output_line)
        print(output_line, end='')

    # Compute GEN and KILL sets
    GEN = defaultdict(set)
    KILL = defaultdict(set)
    for block_name, instructions in blocks:
        defined_vars = set()
        for line, instruction in instructions:
            if "=" in instruction and "if" not in instruction and "goto" not in instruction and "return" not in instruction:
                variable = instruction.split("=")[0].strip()
                if "[" in variable:
                    variable = f"x[{variable.split('[')[1].split(']')[0]}]"
                # Find the definition ID
                for def_key, (defined_variable, definition_line, definition_instruction) in definitions.items():
                    if defined_variable == variable and definition_line == line:
                        GEN[block_name].add(def_key)
                defined_vars.add(variable)
        # KILL: Definitions of the same variable that are not in GEN
        for var in defined_vars:
            for def_key, (defined_variable, definition_line, definition_instruction) in definitions.items():
                if defined_variable == var:
                    found = False
                    for line, instruction in instructions:
                        if def_key in GEN[block_name]:
                            found = True
                            break
                    if not found:
                        KILL[block_name].add(def_key)

    # Iterative Reaching Definitions
    IN_rd = defaultdict(set)
    OUT_rd = defaultdict(set)
    # Initialize OUT with GEN
    for block_name, instructions in blocks:
        OUT_rd[block_name] = GEN[block_name].copy()

    changed = True
    iteration_rd = 1
    output_file.write("\nForward Flow Analysis:\n")
    print("\nForward Flow Analysis:")
    while changed:
        changed = False
        iteration_header = f"\nIteration {iteration_rd}:\n"
        output_file.write(iteration_header)
        print(iteration_header, end='')
        for block_name, instructions in blocks:
            # IN = union of OUT of predecessors
            new_IN = set()
            for pred in predecessors[block_name]:
                new_IN.update(OUT_rd[pred])
            if new_IN != IN_rd[block_name]:
                IN_rd[block_name] = new_IN
                changed = True
            # OUT = GEN ∪ (IN - KILL)
            new_OUT = GEN[block_name].union(IN_rd[block_name].difference(KILL[block_name]))
            if new_OUT != OUT_rd[block_name]:
                OUT_rd[block_name] = new_OUT
                changed = True
            # Sort the sets for consistent display
            in_sorted = sorted(IN_rd[block_name])
            out_sorted = sorted(OUT_rd[block_name])
            output_line = f"{block_name}: IN = {{{', '.join(in_sorted)}}}, OUT = {{{', '.join(out_sorted)}}}\n"
            output_file.write(output_line)
            print(output_line, end='')
        iteration_rd += 1
    convergence_message = f"Convergence reached after {iteration_rd - 1} iterations.\n"
    output_file.write(convergence_message)
    print(convergence_message)

def liveVariableAnalysis(blocks, successors, output_file):
    # Step 5: Live Variables Analysis
    # USE and DEF sets
    USE = defaultdict(set)
    DEF = defaultdict(set)
    for block_name, instructions in blocks:
        defined = set()
        for line, instruction in reversed(instructions):  # Process in reverse for USE before DEF
            # DEF: Variables defined
            if "=" in instruction and "if" not in instruction and "goto" not in instruction and "return" not in instruction:
                variable = instruction.split("=")[0].strip()
                if "[" in variable:
                    variable = f"x[{variable.split('[')[1].split(']')[0]}]"
                DEF[block_name].add(variable)
                defined.add(variable)
            # USE: Variables used before defined
            if "=" in instruction and "return" not in instruction:
                rhs = instruction.split("=")[1].strip()
                # Extract variables (simplified)
                for var in rhs.split():
                    var = var.strip()
                    if var in ["+", "-", "*", "0.0", "1.0", "1", "2", "4", "8", "10", "88"]:
                        continue
                    # Handle array indices (e.g., x[T2] uses T2)
                    if "[" in var:
                        index_variable = var.split("[")[1].split("]")[0]
                        if index_variable not in defined:
                            USE[block_name].add(index_variable)
                    # Handle regular variables (e.g., i, j, T1)
                    elif var.isalnum() and var not in defined:
                        USE[block_name].add(var)
            if "if" in instruction:
                condition = instruction.split("then")[0].replace("if", "").strip()
                for var in condition.split():
                    var = var.strip()
                    if var in ["<", "<=", "=", ">=", ">", "2", "1", "10"]:
                        continue
                    if var not in defined:
                        USE[block_name].add(var)

    # Iterative Live Variables
    IN_lv = defaultdict(set)
    OUT_lv = defaultdict(set)
    # Initialize IN with USE
    for block_name, instructions in blocks:
        IN_lv[block_name] = USE[block_name].copy()

    changed = True
    iteration_lv = 1
    output_file.write("\nBackward Flow Analysis:\n")
    print("\nBackward Flow Analysis:")
    while changed:
        changed = False
        iteration_header = f"\nIteration {iteration_lv}:\n"
        output_file.write(iteration_header)
        print(iteration_header, end='')
        for block_name, instructions in blocks:
            # OUT = union of IN of successors
            new_OUT = set()
            for succ in successors[block_name]:
                new_OUT.update(IN_lv[succ])
            if new_OUT != OUT_lv[block_name]:
                OUT_lv[block_name] = new_OUT
                changed = True
            # IN = USE ∪ (OUT - DEF)
            new_IN = USE[block_name].union(OUT_lv[block_name].difference(DEF[block_name]))
            if new_IN != IN_lv[block_name]:
                IN_lv[block_name] = new_IN
                changed = True
            # Sort the sets for consistent display
            in_sorted = sorted(IN_lv[block_name])
            out_sorted = sorted(OUT_lv[block_name])
            output_line = f"{block_name}: IN = {{{', '.join(in_sorted)}}}, OUT = {{{', '.join(out_sorted)}}}\n"
            output_file.write(output_line)
            print(output_line, end='')
        iteration_lv += 1
    convergence_message = f"Convergence reached after {iteration_lv - 1} iterations.\n"
    output_file.write(convergence_message)
    print(convergence_message)

def processTestCase(filename, output_filename):
         
    # Open the output file for writing
    with open(output_filename, 'w') as output_file:
        
        sep1 = "\n==============================================================================================================="
        sep2 = "\n==============================================================================================================="
        header = sep1 + sep1 + f"\n\n=== Test Case: {filename} ===\n"
        output_file.write(header)
        print(header, end='')       

        # Read the TAC instructions from the file
        with open(filename, 'r') as file:
            allInstructions = file.readlines()

        # Get all leaders
        leaders = getAllLeadersSorted(allInstructions)

        # Construct basic blocks
        blocks, block_map = constructAllBasicBlocks(allInstructions, leaders)

        # Construct CFG
        successors, predecessors = constructCFG(blocks, block_map, allInstructions)
        
        #  Print the CFG
        output_file.write("\nControl Flow Graph:\n")
        print("\nControl Flow Graph:")
        for block_name, instructions in blocks:
            block_line = f"{block_name}: {instructions}\n"
            output_file.write(block_line)
            print(block_line, end='')
            successors_line = f"  Successors: {successors[block_name]}\n"
            output_file.write(successors_line)
            print(successors_line, end='')

        # Perform Forward Flow Analysis
        reachingDefinitionsAnalysis(blocks, predecessors, output_file)

        # Perform Live Variables analysis
        liveVariableAnalysis(blocks, successors, output_file)

if __name__ == '__main__':
    # List of test case files and their respective output files
    testCases = [
        ('test1.txt', 'test1_output.txt'),
        ('test2.txt', 'test2_output.txt'),
        ('test3.txt', 'test3_output.txt')
    ]

    # Process each test case and write output to the respective file
    for testFile, outputFile in testCases:
        processTestCase(testFile, outputFile)