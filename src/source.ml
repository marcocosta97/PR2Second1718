
type ide = string;;

type exp = Eint of int 
         | Ebool of bool
         | Den of ide
         | Sum of exp * exp
         | Sub of exp * exp
         | Mul of exp * exp
         | And of exp * exp
         | Or of exp * exp
         | Not of exp
         | Eq of exp * exp
         | IsZero of exp
         | Ifthenelse of exp * exp * exp
         | Let of ide * exp * exp
         | Letrec of ide * ide * exp * exp
         | Fun of ide * exp
         | App of exp * exp
         (*---*)
         | ETree of tree
         | ApplyOver of exp * exp
         | Update of (ide list) * exp * exp
         | Select of (ide list) * exp * exp
and tree = Empty
         | Node of ide * exp * tree * tree
;;

(* interprete fornito *)

type 't env = (ide * 't) list;;

type evT = Int of int 
         | Bool of bool 
         | Closure of ide * exp * evT env
         | Recclosure of ide * ide * exp * evT env 
         | Unbound
         | EvalTree of evNode
and evNode = Empty | ENode of ide * evT * evNode * evNode ;;

let rec typecheck (a, b) = match (a, b) with
  | ("int", Int(n)) -> true
  | ("bool", Bool(n)) -> true
  | _ -> false;;

let int_plus (x, y) = match (typecheck("int", x), typecheck("int", y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v + w)
  | (_,_,_, _) -> failwith "not compatible";;

let int_minus (x, y) = match (typecheck("int", x), typecheck("int", y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v - w)
  | (_,_,_, _) -> failwith "not compatible";;

let int_mul (x, y) = match (typecheck("int", x), typecheck("int", y), x, y) with
  | (true, true, Int(v), Int(w)) -> Int(v * w)
  | (_,_,_, _) -> failwith "not compatible";;

let bool_and (x, y) = match (typecheck("bool", x), typecheck("bool", y), x, y) with
  | (true, true, Bool(v), Bool(w)) -> Bool(v && w)
  | (_,_,_, _) -> failwith "not compatible";;

let bool_or (x, y) = match (typecheck("bool", x), typecheck("bool", y), x, y) with
  | (true, true, Bool(v), Bool(w)) -> Bool(v || w)
  | (_,_,_, _) -> failwith "not compatible";;

let bool_not x = match (typecheck("bool", x), x) with
  | (true, Bool(v)) -> Bool(not v)
  | (_,_) -> failwith "not compatible";;

let eq (x, y) = match (x, y) with
  | (Int(e1), Int(e2)) -> if e1 = e2 then Bool(true) else Bool(false)
  | (Bool(b1), Bool(b2)) -> Bool(b1 = b2)
  | _ -> failwith "eq not possible";;

let int_iszero x = match (typecheck("int", x), x) with
  | (true, Int(n)) -> Bool(n = 0)
  | _ -> failwith "not compatible";;
let rec lookup (e : 't env) s = match e with
  | [] -> Unbound
  | (s1, d)::e2 -> if s = s1 then d else lookup e2 s;;

let bind (e : 't env) s d = (s, d) :: e;; 

let emptyEnv = [("", Unbound)];;

let rec eval ((e : exp), (env : evT env)) = match e with
  | Eint(n) -> Int(n)
  | Ebool(b) -> Bool(b)
  | Den(s) -> lookup env s
  | Sum(e1, e2) -> int_plus(eval(e1, env), eval(e2, env))
  | Sub(e1, e2) -> int_minus(eval(e1, env), eval(e2, env))
  | Mul(e1, e2) -> int_mul(eval(e1, env), eval(e2, env))
  | And(e1, e2) -> bool_and(eval(e1, env), eval(e2, env))
  | Or(e1, e2) -> bool_or(eval(e1, env), eval(e2, env))
  | Not(e1) -> bool_not(eval(e1, env))
  | Eq(e1, e2) -> eq(eval(e1, env), eval(e2, env))
  | IsZero(e1) -> int_iszero(eval(e1, env))
  | Ifthenelse(e1, e2, e3) -> let v = eval (e1, env) 
    in (match (typecheck("bool", v), v) with
        | (true, Bool(true)) -> eval(e2, env) 
        | (true, Bool(false)) -> eval(e3, env)
        | (_, _) -> failwith "non-boolean guard")
  | Let(i, e1, e2) -> let env1 = bind env i (eval(e1, env)) in eval(e2, env1) 
  | Letrec(f, x, exp, body) -> (let renv = bind env f (Recclosure(f, x, exp, env)) in
                                eval(body, renv))
  | Fun(par, e) -> Closure(par, e, env)
  | App(fide, par) -> (let fclosure = eval(fide, env) in match fclosure with
    | Closure(p, e, fenv) -> (let env2 = bind fenv p (eval (par, env)) 
                              in eval (e, env2))
    | Recclosure(f, x, exp, renv) -> (let env2 = bind renv x (eval(par, env)) in
                                      let env3 = bind env2 f fclosure in
                                      eval(exp, env3))                         
    | _ -> failwith "non functional value") 
  (* inizio progetto *)
  | ETree(t) -> EvalTree(treeval t env)
  | ApplyOver(f, ext) -> let fclosure = eval (f, env) in (match (fclosure, eval(ext, env)) with
      | (Recclosure(_), EvalTree(t))
      | (Closure(_), EvalTree(t)) -> let rec app x = (match x with 
          | ENode(id, exp, ls, rs) -> (ENode(id, appf fclosure exp, app ls, app rs))
          | Empty -> Empty) in EvalTree(app t)    
      | (Closure(_), _)
      | (Recclosure(_), _) -> failwith "not a tree"
      | (_, EvalTree(t)) -> failwith "not a function"
      | (_, _) -> failwith "impossible to evaluate")
  | Update(l, f, ext) -> (let fclosure = eval(f, env) in match fclosure with 
    | Closure(_)
    | Recclosure(_) -> (match eval(ext, env) with 
        | EvalTree(t) -> EvalTree(updatePath l t fclosure)
        | _ -> failwith "not a tree" ) 
    | _ -> failwith "not a function")
  | Select(l, f, ext) -> (let fclosure = eval(f, env) in match fclosure with 
    | Closure(_)
    | Recclosure(_) -> (match eval(ext, env) with 
        | EvalTree(t) -> obtainSubTree l t fclosure
        | _ -> failwith "not a tree")
    | _ -> failwith "not a function")

(* 
  tree -> evT env -> evNode

  valutazione ricorsiva dei nodi dell'albero
*)
and treeval t env = match t with
  | Node(id, exp, ls, rs) -> ENode(id, eval (exp, env) , (treeval ls env), (treeval rs env))
  | Empty -> Empty
(*
  evT -> evT -> evT env -> evT

  data una chiusura e un tipo esprimibile, restituisce la valutazione della chiusura dove vi
  è associato il tipo esprimibile come parametro 
  (scoping statico)  
*)
and appf fclosure exp = match fclosure with 
  | (Closure(p, e, fenv)) -> (let env2 = bind fenv p exp 
                              in eval(e, env2))
  | (Recclosure(f, y, e, renv)) -> (let env2 = bind renv y exp in 
                                    let env3 = bind env2 f fclosure in 
                                    eval(e, env3))
  | _ -> failwith "can't apply"

(*
  ide list -> evNode -> evT -> evT env -> evNode

  dato un cammino, la radice e la chiusura restituisce un albero
  con il nodo identificato dal cammino aggiornato e valutato sse esiste un cammino che identifica il nodo
  altrimenti non viene aggiornato
*)  
and updatePath l ext f = match (l, ext) with 
  | (first :: [], ENode(id, exp, ls, rs)) -> if id = first then ENode(id, appf f exp, ls, rs) 
    else ext
  | (first :: rest, ENode(id, exp, ls, rs)) -> if id = first 
    then ENode(id, exp, updatePath rest ls f , updatePath rest rs f)
    else ext
  | (_, _) -> ext  

(* 
  ide list -> evNode -> evT -> evT env -> evT

  dato un cammino, la radice e la chiusura restituisce un albero
  con radice il nodo evidenziato dal cammino sse la funzione è verificata
  altrimenti restituisce un albero vuoto
*)
and obtainSubTree l ext f = match (l, ext) with 
  | (first :: [], ENode(id, exp, ls, rs)) -> if not (first = id) then EvalTree(Empty) 
    else (let boolres = match appf f exp with 
        | Bool(w) -> w
        | _ -> false in (if boolres then EvalTree(ext) else EvalTree(Empty)))
  | (first :: rest, ENode(id, exp, ls, rs)) -> if not (first = id) then EvalTree(Empty)
    else (let t1 = obtainSubTree rest ls f in 
          let t2 = obtainSubTree rest rs f in (match (t1, t2) with 
        | (EvalTree(Empty), EvalTree(Empty)) -> EvalTree(Empty)
        | (EvalTree(ENode(_)), _ ) -> t1
        | (_, EvalTree(ENode(_))) -> t2
        | _ -> failwith "incompatible types" ))
  | (_, _) -> EvalTree(Empty)
;;

