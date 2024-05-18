# OCaml Subset Interpreter

This project is a full interpreter for a subset of OCaml, featuring parsing and lexing capabilities. The interpreter is designed to understand and execute a carefully selected subset of OCaml, making it ideal for learning about language design and implementation.

## Features

### Lexical Analysis (Lexing)
Lexical analysis, or lexing, is the first phase of the interpreter. During this phase, the source code is scanned to convert sequences of characters into meaningful tokens. Tokens are the smallest units of meaning, such as keywords, operators, identifiers, and literals. The lexer discards whitespace and comments, focusing only on the significant parts of the code.

- **Tokenization**: The lexer processes the input OCaml code, breaking it down into a stream of tokens.
- **Error Handling**: It detects lexical errors, such as invalid characters, and provides informative error messages.

### Syntax Analysis (Parsing)
Syntax analysis, or parsing, takes the stream of tokens produced by the lexer and arranges them into a structured format called an abstract syntax tree (AST). The AST represents the hierarchical syntactic structure of the source code, making it easier to analyze and interpret.

- **Grammar Rules**: The parser uses a set of grammar rules to ensure the code conforms to the expected syntax of the OCaml subset.
- **AST Generation**: It constructs an AST, where each node represents a language construct (e.g., expressions, statements, function definitions).
- **Error Handling**: The parser identifies and reports syntax errors, such as missing parentheses or unexpected tokens.

### Evaluation
The evaluation phase is where the interpreter executes the program based on the AST generated by the parser. This phase involves traversing the AST and performing computations according to the semantics of the OCaml subset.

- **Expression Evaluation**: It computes the value of expressions, including arithmetic operations, logical operations, and function calls.
- **Variable Binding**: The interpreter manages variable scope and bindings, ensuring that variables are correctly assigned and accessed.
- **Function Execution**: It handles the execution of functions, including recursive calls and parameter passing.
- **Control Flow**: The interpreter manages control flow constructs such as conditionals (if-else statements) and loops.

By implementing these features, the OCaml Subset Interpreter provides a robust framework for understanding the key components of language interpretation, making it a valuable tool for educational purposes and experimentation with language design.
