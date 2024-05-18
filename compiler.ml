(* disable unused constructor warning *)
[@@@warning "-37"]

(*
we follow the general procedure:
  string
  -> lexing
  tokens
  -> parsing
  abstract syntax tree
  -> type checking
  abstract syntax tree
  -> evaluation
  value




Compared to template:
- reordering to follow passes
- rewrote lexer
- more space between parts
- added comments

Alternatives:
- handle true false as individual tokens
- app could be a binary operator
- we could split parser exceptions into multiple exceptions
*)




(* types and definitions *)

(* lexer *)
type token =
  | ADD
  | SUB
  | MUL
  | LEQ
  | LP
  | RP
  | EQ
  | ARROW
  | LET
  | REC
  | IN
  | FUN
  | IF
  | THEN
  | ELSE
  | INT
  | BOOL
  | VAR of string
  | ICON of int
  | BCON of bool
  | COLON

(* parser and afterward *)
type op = Add | Sub | Mul | Leq
type ty = Int | Bool | Fun of ty * ty

type exp =
  | Icon of int
  | Bcon of bool
  | Var of string
  | Binary of op * exp * exp
  | If of exp * exp * exp
  | Let of string * exp * exp
  | Lam of string * ty * exp
  | App of exp * exp
  | Letrec of string * string * ty * ty * exp * exp


type 'b env = (string * 'b) list

(* type checking *)
type tenv = ty env

(* Evaluator *)
type va =
  | Ival of int
  | Bval of bool
  | Cl of string * exp * venv
  | Cr of string * string * exp * venv

and venv = va env

;;
exception EvalError of string
exception LexError of string*char list
exception ParseError of string*token list
;;

(* general helper functions *)
(* environments -- like List.assoc but easier swapable *)
let rec lookup k env =
  match env with
  | [] -> None
  | (k', v) :: l -> if k = k' then Some v else lookup k l

let rec update k v env =
  match env with
  | [] -> [ (k, v) ]
  | (k', v') :: l -> if k = k' then (k, v) :: l else (k', v') :: update k v l

let explode s = List.of_seq (String.to_seq s)


;;









(* Lexer 
   converts a string into a list of tokens

   changes to template:
   - we use a char list instead of a string
   - we use a exception instead of a general failure
*)

let is_digit c = '0' <= c && c <= '9'
let is_lowercase c = 'a' <= c && c <= 'z'
let is_uppercase c = 'A' <= c && c <= 'Z'
let is_whitespace c = c = ' ' || c = '\n' || c = '\t'

(* leave negative numbers apart for parsing *)
let lex_num xs =
  let rec lex_num' i xs =
    match xs with
    | [] -> i, []
    | c::xs when is_digit c -> 
      let i' = i*10 + Char.code c - Char.code '0' in
      lex_num' i' xs
    (* reject 1a -> only whitespace, parentheses, operators, ... allowed; no identifiers *)
    | c::xs when is_lowercase c -> raise (LexError ("illegal identifier after number", xs))
    | _ -> i, xs
  in
  lex_num' 0 xs

let keywords = [
  "let", LET;
  "in", IN;
  "if", IF;
  "then", THEN;
  "else", ELSE;
  "true", BCON true;
  "false", BCON false;
  "fun", FUN;
  "rec", REC;
  "int", INT;
  "bool", BOOL;
]

let lex_id xs =
  let valid c = 
    is_digit c ||
    is_lowercase c ||
    is_uppercase c ||
    c = '_' ||
    c = '\''
  in
  let rec lex_id' s xs =
    match xs with
    | [] -> s, []
    | c::xs when valid c ->
      let s' = s ^ String.make 1 c in
      lex_id' s' xs
    | _ -> s, xs
  in
  let s, xs = lex_id' "" xs in
  match lookup s keywords with
  | Some t -> t, xs
  | None -> VAR s, xs

let rec lex' = function
  (* like keywords but lex away directly and greedily *)
  | '+'::s -> ADD :: lex' s
  | '-'::'>'::s -> ARROW :: lex' s
  | '-'::s -> SUB :: lex' s
  | '*'::s -> MUL :: lex' s
  | '('::s -> LP :: lex' s
  | ')'::s -> RP :: lex' s
  | '='::s -> EQ :: lex' s
  | ':'::s -> COLON :: lex' s
  | '<'::'='::s -> LEQ :: lex' s
  | '<'::s -> raise (LexError ("illegal <", s))
  | c::s when is_whitespace c -> lex' s
  | c::s when is_digit c -> 
    let i, s' = lex_num (c::s) in
    ICON i :: lex' s'
  | c::s when is_lowercase c -> 
    let t, s = lex_id (c::s) in
    t :: lex' s
  | c::s -> raise (LexError ("illegal character " ^ String.make 1 c, s))
  | [] -> []

let lex s = lex' (explode s)

;;




let show_token = function
  | ADD -> "ADD"
  | SUB -> "SUB"
  | MUL -> "MUL"
  | LEQ -> "LEQ"
  | LP -> "LP"
  | RP -> "RP"
  | EQ -> "EQ"
  | ARROW -> "ARROW"
  | LET -> "LET"
  | REC -> "REC"
  | IN -> "IN"
  | FUN -> "FUN"
  | IF -> "IF"
  | THEN -> "THEN"
  | ELSE -> "ELSE"
  | INT -> "INT"
  | BOOL -> "BOOL"
  | VAR x -> "VAR " ^ x
  | ICON i -> "ICON " ^ string_of_int i
  | BCON b -> "BCON " ^ string_of_bool b
  | COLON -> "COLON"

(* let show_list show xs = "[" ^ String.concat "; " (List.map show xs) ^ "]"
let show_token_list = show_list show_token *)




(* Parser 
   
Compared to template:
- custom error message

*)


let expect_id ts =
  match ts with VAR x :: ts -> (x, ts) | _ -> raise (ParseError ("expected id", ts))

let expect t ts =
  match ts with 
  | t' :: ts when t = t' -> ts 
  | t' :: _ -> raise (ParseError ("expected " ^ show_token t ^ " but got " ^ show_token t', ts))
  | [] -> raise (ParseError ("expected " ^ show_token t ^ " but got nothing", ts))



(* 
  custom type parser to make code more readable
  ty ::= pty | pty -> ty
  pty ::= int | bool | (ty) 

  a student not understanding the precedence parser is helped more
  by doing it manuall instead of incorporating it into the precedence parser
  (writing new is easier although slightly more code)

let ty_op = function
  | ARROW :: ts -> Some ((fun l r -> Fun (l, r)), 2, 1, ts)
  | _ -> None

let pty = function
  | BOOL :: ts -> (Bool, ts)
  | INT :: ts -> (Int, ts)
  | LP :: ts ->
      let ty, ts = parse_ty ts in
      let ts = expect RP ts in
      (ty, ts)
  | _ as ts -> raise (Expected ("type", ts))

let parse_ty ts = binary pty ty_op ts
*)
let rec parse_ty ts =
  let ty, ts = parse_pty ts in
  match ts with
  | ARROW :: ts ->
      let ty', ts = parse_ty ts in
      (Fun (ty, ty'), ts)
  | _ -> (ty, ts)
and parse_pty ts =
  match ts with
  | INT :: ts -> (Int, ts)
  | BOOL :: ts -> (Bool, ts)
  | LP :: ts ->
      let ty, ts = parse_ty ts in
      let ts = expect RP ts in
      (ty, ts)
  | _ -> raise (ParseError ("expected type", ts))


(* operator precedence parser *)
let parse_binary parse_simpl parse_op ts =
  (* parse binary expression at operator priority level p *)
  let rec binary p (l, ts) =
    (* Check if the next token is an operator *)
    match parse_op ts with
    (* if the next token is not an operator, return the expression parsed so far *)
    | None -> (l, ts)
    (* If the next token is an operator, it returns the operator 
    (type Op), its left and right priority, and the remaining token stream *)
    | Some (op, lp, rp, ts') ->
        (* if the left prio is less than the current one
        return the expr parsed so far. Else continue
        parsing with the right prio and build the expr. *)
        if lp < p then (l, ts)
        else
          let r, ts = binary rp (parse_simpl ts') in
          binary p (op l r, ts)
  in
  binary 0 (parse_simpl ts)


let parse_op ts =
  let create op l r = Binary (op, l, r) in
  match ts with
  | LEQ :: ts -> Some (create Leq, 0, 1, ts)
  | ADD :: ts -> Some (create Add, 2, 3, ts)
  | SUB :: ts -> Some (create Sub, 2, 3, ts)
  | MUL :: ts -> Some (create Mul, 4, 5, ts)
  (* student code for app as binary operator *)
  | ICON _ :: _ 
  | BCON _ :: _ 
  | VAR _ :: _
  | LP :: _ -> Some ((fun l r -> App (l, r)), 5, 6, ts)
  | _ -> None

let rec parse_expr ts = parse_binary parse_simple_expr parse_op ts

and parse_simple_expr ts =
  match ts with
  | ICON c :: ts -> (Icon c, ts)
  | BCON c :: ts -> (Bcon c, ts)
  | VAR x :: ts -> (Var x, ts)
  | IF :: ts ->
      let e1, ts = parse_expr ts in
      let ts = expect THEN ts in
      let e2, ts = parse_expr ts in
      let ts = expect ELSE ts in
      let e3, ts = parse_expr ts in
      (If (e1, e2, e3), ts)
  | LP  :: ts -> let e, ts = parse_expr ts in      (* ( expr *)
                 let ts = expect RP ts in (e, ts)  (* ) *)
  | LET :: REC :: ts ->                            (* let rec *)
                 let f,  ts = expect_id ts in      (* f  *)
                 let     ts = expect LP ts in      (* (  *)
                 let x,  ts = expect_id ts in      (* x  *)
                 let     ts = expect COLON ts in   (* :  *)   
                 let t1, ts = parse_ty ts in       (* t  *)
                 let     ts = expect RP ts in      (* )  *)
                 let     ts = expect COLON ts in   (* :  *)    
                 let t2, ts = parse_ty ts in       (* t  *)
                 let     ts = expect EQ ts in      (* =  *)
                 let e1, ts = parse_expr ts in     (* e  *)  
                 let     ts = expect IN ts in      (* in *)
                 let e2, ts = parse_expr ts in     (* e  *)  
                 Letrec (f, x, t1, t2, e1, e2), ts 
  | FUN :: ts -> let     ts = expect LP ts in      (* fun ( *)
                 let x,  ts = expect_id ts in      (* x  *)
                 let     ts = expect COLON ts in   (* :  *)  
                 let t,  ts = parse_ty ts in       (* t  *)
                 let     ts = expect RP ts in      (* )  *)
                 let     ts = expect ARROW ts in   (* -> *)   
                 let e,  ts = parse_expr ts in     (* e  *) 
                 Lam (x, t, e), ts                
  | LET :: ts ->
      let x, ts = expect_id ts in
      let ts = expect EQ ts in
      let e1, ts = parse_expr ts in
      let ts = expect IN ts in
      let e2, ts = parse_expr ts in
      (Let (x, e1, e2), ts)
  | _ -> raise (ParseError ("expected simple expr", ts))

let parse ts = 
  match parse_expr ts with
  | e, [] -> e
  | _, ts -> raise (ParseError ("expected end of input", ts))
;;










  (* Type checking (Elaboration) *)

let rec check_ty (env : tenv) (e : exp) =
  match e with
  | Icon _ -> Some Int
  | Bcon _ -> Some Bool
  | Var x -> lookup x env
  | If (e1, e2, e3) ->
      let t1 = check_ty env e1 in
      let t2 = check_ty env e2 in
      let t3 = check_ty env e3 in
      (match t1, t2, t3 with
      | Some Bool, Some t2, Some t3 -> if t2 = t3 then Some t2 else None
      | _ -> None)
  | Let (x, e1, e2) -> (
      let t1 = check_ty env e1 in
      match t1 with
      | Some t1 ->
          let env' = update x t1 env in
          check_ty env' e2
      | None -> None)
  | Binary (op, e1, e2) ->
      let t1 = check_ty env e1 in
      let t2 = check_ty env e2 in
      if t1 = Some Int && t2 = Some Int then
        Some (match op with Leq -> Bool | _ -> Int)
      else None
  | App (e1, e2) ->
      let t1 = check_ty env e1 in
      let t2 = check_ty env e2 in
      (match t1 with
      | Some (Fun (t1, t2')) when t2 = Some t1 -> Some t2'
      | _ -> None)
  | Lam (x, t1, e) ->
      let env' = update x t1 env in
      let t2 = check_ty env' e in
      (match t2 with
      | Some t2' -> Some (Fun (t1, t2'))
      | None -> None)
  | Letrec (f, x, t1, t2, e1, e2) ->
      let env' = update f (Fun (t1, t2)) env in
      let env'' = update x t1 env' in
      let tf = check_ty env'' e1 in
      let tb = check_ty env' e2 in
      if tf <> Some t2 then None else tb
;;






(* Evaluation *)
let rec eval (env : venv) (e : exp) =
  match e with
  | Icon c -> Ival c
  | Bcon b -> Bval b
  | Var x -> (
      match lookup x env with
      | Some v -> v
      | None -> raise (EvalError ("unbound variable " ^ x)))
  | If (e1, e2, e3) -> (
      match eval env e1 with
      | Bval true -> eval env e2
      | Bval false -> eval env e3
      | _ -> raise (EvalError "illegal val in if"))
  | Let (x, e1, e2) ->
      let v = eval env e1 in
      let env' = update x v env in
      eval env' e2
  | Binary (op, e1, e2) -> (
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      match (op, v1, v2) with
      | Add, Ival x, Ival y -> Ival (x + y)
      | Sub, Ival x, Ival y -> Ival (x - y)
      | Mul, Ival x, Ival y -> Ival (x * y)
      | Leq, Ival x, Ival y -> Bval (x <= y)
      | _ -> raise (EvalError "illegal operator/value in binary"))
  | App (e1, e2) -> (
      let v1 = eval env e1 in
      let v2 = eval env e2 in
      match v1 with
      | Cl (x, e, env') -> eval (update x v2 env') e
      | Cr (f, x, e, env') -> eval (update f v1 (update x v2 env')) e
      | _ -> raise (EvalError "illegal value in app"))
  | Lam (x, _t, e) -> Cl (x, e, env)
  | Letrec (f, x, _t1, _t2, e1, e2) ->
      let env' = update f (Cr (f, x, e1, env)) env in
      eval env' e2
  

let [@warning "-32"] eval_checked tenv venv e =
  match check_ty tenv e with
  | Some _ -> eval venv e
  | None -> failwith "program ill-typed"
;;

