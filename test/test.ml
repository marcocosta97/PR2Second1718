(* =============================  TESTS  ============================= *)

(* applicazione della funzione f x = x * 10 *)
let t1 = ApplyOver(Fun("x", Mul(Den("x"), Eint 10)), ETree(Node("a",Eint 1, Node("b", Eint 2, Empty, Empty), Node("c", Eint 3, Empty, Empty))));;

eval(t1, emptyEnv);;

(* tentativo di applicazione di una funzione su un nodo contenente una chiusura, operazione non permessa*)
let t2 = ApplyOver(Fun("x", Mul(Den("x"), Eint 10)), ETree(Node("a", Fun("x", Sum(Eint 1, Den "x")), Node("b", Eint 2, Empty, Empty), Node("c", Eint 3, Empty, Empty))));;

(* eval(t2, emptyEnv);; *)

(* applicazione di funzione con risoluzione tramite scoping statico *)
let t3 = Let("y", Eint 3, Let("z", Fun("x", Sum(Den("y"), Den("x"))), Let("y", Eint 100, ApplyOver(Den "z", ETree(Node("a", Eint 12, Node("b", Eint 2, Empty, Empty), Node("c", Eint 3, Empty, Empty)))))));;

eval(t3, emptyEnv);;

(* aggiornamento effettuato su due cammini possibili *)
let t4 = Update(["a"; "b"; "c"], Fun("x", Ebool(true)), ETree(Node("a", Eint 10, Node("b", Eint 20, Node("c", Eint 30, Empty, Empty), Empty), Node("b", Eint 40, Empty, Node("c", Eint 10, Empty, Empty)))));;

eval(t4, emptyEnv);;

(* selezione *)
let t5 = Select(["a"; "b"], Fun("x", Eq(Den("x"), Eint 100)), 
                ETree(Node("a", Eint 12, Node("b", Eint 100, Node("c", Eint 5, Empty, Empty), Empty), Node("b", Eint 3, Empty, Node("c", Eint 10, Empty, Empty)))));;

eval(t5, emptyEnv);;

(* applicazione della funzione fattoriale ricorsiva sull'albero *)
let trec = Letrec("fact", "n", Ifthenelse(Eq(Den("n"), Eint(0)), Eint(1), Mul(Den("n"), App(Den("fact"), Sub(Den("n"), Eint(1))))), 
                  ApplyOver(Den "fact",
                            ETree(Node("a", Eint 1, Node("b", Eint 2, Node("d", Eint 3, Empty, Empty), Node("c", Eint 4, Empty, Empty)), Node("c", Eint 5, Empty, Empty)))));;

eval(trec, emptyEnv);;