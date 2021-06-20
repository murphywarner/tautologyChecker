(* PROPOSITION. Represent an expression in propositional logic. *)

type proposition =
    False |
    True |
    Var of string | 
    And of proposition * proposition |
    Or of proposition * proposition |
    Not of proposition |
    Imply of proposition * proposition |  
    Equiv of proposition * proposition ;;
    
    (* CONDITIONAL. Represent an IF term. *)
type conditional =
    IffyFalse |
    IffyTrue |
    IffyVar of string |
    If of conditional * conditional * conditional ;;

let q1=
  (Imply
     (Not
        (And        
           (Var "p", Var "q")),
      Or
        (Not        
           (Var "p"),
         Not      
           (Var "q")))) ;;

let q2 =
  (And
     (Var "p", Var "q")) ;;
    (* Beware: Q1 and Q2 are not exhaustive tests! Your code is not necessarily
correct if it works on them. *)

let q3 = (Or (Var "p", Not (Var "p")));;

let q4 = (Imply (Var "p",Var "q"));;

let q5 = If (IffyVar "p", IffyVar "q", IffyFalse) ;;

let rec ifify p = 
  match p with
    False -> IffyFalse |
    True -> IffyTrue | 
    Var(s) -> IffyVar(s) |
    Not(prop) -> If(ifify prop, IffyFalse, IffyTrue) |
    And(prop1,prop2) -> If(ifify prop1, ifify prop2, IffyFalse) |
    Or(prop1, prop2) -> If(ifify prop1, IffyTrue, ifify prop2) |
    Imply(prop1, prop2) -> If(ifify(prop1), ifify(prop2), IffyTrue) |
    Equiv(prop1, prop2) -> If(ifify(prop1), ifify(prop2), If(ifify(prop2), IffyFalse, IffyTrue)) ;;

let rec normalize term =
  let rec normalizing pi1 alpha1 beta1 =
    match pi1
    with If (pi0, alpha0, beta0) -> normalize(If(normalize pi0, normalizing alpha0 alpha1 beta1, normalizing beta0 alpha1 beta1))|
      _ ->
        If (pi1, normalize alpha1, normalize beta1)
  in match term
  with If (pi, alpha, beta) -> normalizing pi alpha beta |
    _ -> term ;;

let rec substitute c v b = 
  if c = v 
  then b
  else
    match c with 
      If(pi, alpha, beta) -> 
        If(substitute pi v b, substitute alpha v b, substitute beta v b) |
      _ -> c;;

let rec simplify c =
  match c with
    IffyFalse  -> IffyFalse |
    IffyTrue-> IffyTrue | 
    IffyVar(s) -> IffyVar(s) |
    If(test, a, b) -> 
      match (test, simplify(substitute a test IffyTrue), simplify(substitute b test IffyFalse)) with
        (IffyTrue, a, b) -> a |
        (IffyFalse, a, b) -> b | 
        (pi, IffyTrue, IffyFalse) -> pi |
        (pi, alpha, beta) ->
          if alpha = beta
          then alpha 
          else if pi = IffyTrue
          then alpha
          else if pi = IffyFalse
          then beta
          else If(pi, alpha, beta);;

let tautology p = 
  let boolean = 
    simplify (normalize (ifify p)) in if boolean = IffyTrue then true else false;;

(*
   Test Cases for q1-q5
   
   tautology q1 ;;
   - : bool = true
   tautology q2;;
   - : bool = false
   tautology q3;;
   - : bool = true
   tautology q4;;
   - : bool = false
   simplify q5 ;;
   - : conditional = If (IffyVar "p", IffyVar "q", IffyFalse)

   *)