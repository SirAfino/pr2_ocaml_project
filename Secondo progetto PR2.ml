type ide = string;;
type exp = Eint of int | Ebool of bool | Den of ide | Prod of exp * exp | Sum of exp * exp | Diff of exp * exp |
	Eq of exp * exp | Minus of exp | IsZero of exp | Or of exp * exp | And of exp * exp | Not of exp |
	Ifthenelse of exp * exp * exp | Let of ide * exp * exp | Fun of ide * exp | FunCall of exp * exp | EString of string |
	Letrec of ide * exp * exp | Dict of (ide * exp) list | DictGet of exp * ide | DictSet of exp * ide * exp |
	DictRm of exp * ide | DictClear of exp | ApplyOver of exp * exp | DictLen of exp | DictMerge of exp * exp ;;

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
type evT = Int of int | Bool of bool | Unbound | FunVal of evFun | RecFunVal of ide * evFun |
	DictVal of (ide * evT) list | String of string
and evFun = ide * exp * evT env

(*rts*)
(*type checking*)
let typecheck (s : string) (v : evT) : bool = match s with
	"int" -> (match v with
		Int(_) -> true |
		_ -> false) |
	"bool" -> (match v with
		Bool(_) -> true |
		_ -> false) |
	_ -> failwith("not a valid type");;

(*funzioni primitive*)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n*u))
	else failwith("Type error");;

let sum x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n+u))
	else failwith("Type error");;

let diff x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Int(n-u))
	else failwith("Type error");;

let eq x y = if (typecheck "int" x) && (typecheck "int" y)
	then (match (x,y) with
		(Int(n),Int(u)) -> Bool(n=u))
	else failwith("Type error");;

let minus x = if (typecheck "int" x) 
	then (match x with
	   	Int(n) -> Int(-n))
	else failwith("Type error");;

let iszero x = if (typecheck "int" x)
	then (match x with
		Int(n) -> Bool(n=0))
	else failwith("Type error");;

let vel x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> (Bool(b||e)))
	else failwith("Type error");;

let et x y = if (typecheck "bool" x) && (typecheck "bool" y)
	then (match (x,y) with
		(Bool(b),Bool(e)) -> Bool(b&&e))
	else failwith("Type error");;

let non x = if (typecheck "bool" x)
	then (match x with
		Bool(true) -> Bool(false) |
		Bool(false) -> Bool(true))
	else failwith("Type error");;

(*Restituisce true se la chiave (x) è contenuta nella lista di coppie chiave-valore (l)*)
let rec keyPresent (l : (ide * 'a) list) (x : ide) : bool = match l with
	| [] -> false
	| (i,v)::ls -> if x = i then true else keyPresent ls x;;

(*Restituisce true se tutte le chiavi del dizionario sono uniche*)
let rec dictCheck (l : (ide * exp) list) : bool = match l with
	| [] -> true
	| (i,e)::ls -> if keyPresent ls i then false else dictCheck ls;;

(*Funzione ausiliaria per il calcolo della lunghezza di una lista di generici*)
let rec len (l : 'a list) : int = match l with
	| [] -> 0
	| x::xs -> 1 + (len xs);;

(*interprete*)
let rec eval (e : exp) (r : evT env) : evT = match e with
	Eint n -> Int n |
	Ebool b -> Bool b |
	EString s -> String s |
	IsZero a -> iszero (eval a r) |
	Den i -> applyenv r i |
	Eq(a, b) -> eq (eval a r) (eval b r) |
	Prod(a, b) -> prod (eval a r) (eval b r) |
	Sum(a, b) -> sum (eval a r) (eval b r) |
	Diff(a, b) -> diff (eval a r) (eval b r) |
	Minus a -> minus (eval a r) |
	And(a, b) -> et (eval a r) (eval b r) |
	Or(a, b) -> vel (eval a r) (eval b r) |
	Not a -> non (eval a r) |
	Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
				else failwith ("nonboolean guard") |
	Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) |
	Fun(i, a) -> FunVal(i, a, r) |
	FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) |
    Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def")) |
	Dict l -> if dictCheck l
				then DictVal(dictEval l r)
				else failwith("keys must be unique") |
	DictGet(d,i) -> (match (eval d r) with
						| DictVal(l) -> get l i
						| _ -> failwith ("invalid dictionary")) |
	DictSet(d,i,e) -> let v = eval e r in
						(match eval d r with
							| DictVal(l) -> if keyPresent l i
												then DictVal(set l i v)
												else DictVal((i,v)::l)
							| _ -> failwith("invalid dictionary")) |
	DictRm(d,i) -> (match (eval d r) with
					| DictVal(l) -> DictVal(rm l i)
					| _ -> failwith("invalid dictionary")) |
	DictClear(d) -> (match (eval d r) with
					| DictVal(l) -> DictVal([])
					| _ -> failwith("invalid dictionary")) |
	ApplyOver(f,d) -> (match (eval f r, eval d r) with
						| (f,DictVal(l)) -> DictVal(apply f l)
						| _ -> failwith("invalid dictionary")) |
	DictLen(d) -> (match eval d r with
					| DictVal(l) -> Int(len l)
					| _ -> failwith("invalid dictionary")) |
	DictMerge(d1,d2) -> (match (eval d1 r,eval d2 r) with
						| (DictVal(l1),DictVal(l2)) -> DictVal(merge l1 l2)
						| _ -> failwith("invalid dictionary"))
							
(*Funzione ausiliaria per la valutazione di tutti i valori associati agli identificatori del dizionario*)
and dictEval (l : (ide * exp) list) (r : evT env) : (ide * evT) list = match l with
	| [] -> []
	| (i,e)::ls -> let v = (eval e r) in (i,v)::(dictEval ls r)

(*Funzione ausiliaria per la ricerca ricorsia della valore associato ad un identificatore*)
and get (l : (ide * evT) list) (i : ide) : evT = match l with
	| [] -> failwith("invalid identifier")
	| (a,v)::ls -> if a = i then v else get ls i

(*Funzione ausiliaria che setta il valore della chiave (i) a (v)*)
and set (l : (ide * evT) list) (i : ide) (v : evT) : (ide * evT) list = match l with
	| [] -> []
	| (a,b)::ls -> if a = i then (a,v)::ls else (a,b)::(set ls i v)
	
(*Funzione ausiliaria per la rimozione della coppia con chiave (i)*)	
and rm (l : (ide * evT) list) (i : ide) : (ide * evT) list = match l with
	| [] -> []
	| (a,b)::ls -> if a = i then ls else (a,b)::(rm ls i)

(*Funzione ausiliaria per il metodo ApplyOver*)
and apply (f : evT) (l : (ide * evT) list) : (ide * evT) list = match (f,l) with
	| (f1,[]) -> []
	| (FunVal(arg,body,r),(i,v)::ls) -> let v1 = try (eval body (bind r arg v))
											 with error -> v in
												(i,v1)::(apply f ls)
	| (RecFunVal(g, (arg, body, r)),(i,v)::ls) -> let v1 = try (let rEnv = (bind r g f) in
													let aEnv = (bind rEnv arg v) in
														eval body aEnv)
												  with error -> v in
												  (i,v1)::(apply f ls)
	| _ -> failwith("invalid function")

(*Funzione ausiliaria per il merge di due dizionari.
	Notare che se una coppia con la stessa chiava ? presente in entrambe le liste
	allora verr? inserita la coppia presente nella lista l2*)
and merge (l1 : (ide * evT) list) (l2 : (ide * evT) list) : (ide * evT) list = match l2 with
	| [] -> l1
	| (i,v)::xs -> let l3 = if keyPresent l1 i
							then set l1 i v
							else (i,v)::l1 in
						merge l3 xs;;
		
(* =============================  TESTS  ================= *)

(* basico: no let *)
let env0 = emptyenv Unbound;;

let e1 = FunCall(Fun("y", Sum(Den "y", Eint 1)), Eint 3);;

eval e1 env0;;

let e2 = FunCall(Let("x", Eint 2, Fun("y", Sum(Den "y", Den "x"))), Eint 3);;

eval e2 env0;;

(* ================= TEST DIZIONARI =================== *)

let env0 = emptyenv Unbound;;
(*Dict*)

let d1 = Dict [("a",Eint 1);("b",Eint 2);("c",EString "xyz")];;
(* d1 = [(a,1);(b,2);(c,"xyz")] *)
eval d1 env0;;

(*DictSet*)

let d2 = DictSet(d1,"d", Eint 4);;
(* d2 = [(d,4);(a,1);(b,2);(c,"xyz")] *)
let d3 = DictSet(d2,"a",Eint 7);;
(* d3 = [(d,4);(a,7);(b,2);(c,"xyz")] *)
let d4 = DictSet(d3,"b",Ebool true);;
(* d4 = [(d,4);(a,7);(b,true);(c,"xyz")] *)
eval d4 env0;;

(*DictGet*)

let aVal = DictGet(d4,"a");;
(* aVal = 7 *)
eval aVal env0;;

(*DictClear*)

let d5 = DictClear(d4);;
(* d5 = [] *)
eval d5 env0;;

(*ApplyOver*)

let inc = Fun("x",Sum(Den "x",Eint 1));;
let d6 = ApplyOver(inc,d4);;
(* d6 = [(d,5);(a,8);(b,true);(c,"xyz")] *)
eval d6 env0;;

(*DictRm*)

let d7 = DictRm(d6,"c");;
(* d7 = [(d,5);(a,8);(b,true)] *)
eval d7 env0;;

(*DictMerge*)

let d8 = Dict [("e",Ebool false);("d",Eint 18)];;
(* d8 = [(e,false);(d,18)] *)
let d9 = DictMerge(d7,d8);;
(* d9 = [(e,false);(d,18);(a,8);(b,true)] *)
eval d9 env0;;

(*DictLen*)

let dLen = DictLen(d9);;
(* dLen = 4 *)
eval dLen env0;;

(*ApplyOver - Recursive*)

(*Semplice funzione ricorsiva che ritorna la sommatoria da 0 a x*)
let sumx = Ifthenelse(Eq(Den "x",Eint 0),Eint 0,Sum(Den "x",FunCall(Den "f",Diff(Den "x",Eint 1))));;
let d10 = Letrec("f",Fun("x",sumx),ApplyOver(Den "f",d9));;
(* d10 = [(e,false);(d,171);(a,36);(b,true)]*)
eval d10 env0;;