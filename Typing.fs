(*
* TinyML
* Typing.fs: typing algorithms
*)

module TinyML.Typing

open Ast

// basic environment
let gamma0 : scheme env = [
    // int
    ("+", Forall(Set.empty,TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("-", Forall(Set.empty,TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("*", Forall(Set.empty,TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("/", Forall(Set.empty,TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    ("%", Forall(Set.empty,TyArrow (TyInt, TyArrow (TyInt, TyInt))))
    (">", Forall(Set.empty,TyArrow (TyInt, TyArrow(TyInt, TyBool))))
    (">=",Forall(Set.empty, TyArrow (TyInt, TyArrow(TyInt, TyBool))))
    ("<", Forall(Set.empty,TyArrow (TyInt, TyArrow(TyInt, TyBool))))
    ("<=",Forall(Set.empty, TyArrow (TyInt, TyArrow(TyInt, TyBool))))
    ("=", Forall(Set.empty,TyArrow (TyInt, TyArrow(TyInt, TyBool))))
    ("<>",Forall(Set.empty, TyArrow (TyInt, TyArrow(TyInt, TyBool))))
    ("-", Forall(Set.empty,TyArrow (TyInt, TyInt)))

    // float
    ("+", Forall(Set.empty,TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("-", Forall(Set.empty,TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("*", Forall(Set.empty,TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("/", Forall(Set.empty,TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    ("%", Forall(Set.empty,TyArrow (TyFloat, TyArrow (TyFloat, TyFloat))))
    (">", Forall(Set.empty,TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    (">=",Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("<", Forall(Set.empty,TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("<=",Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("=", Forall(Set.empty,TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("<>",Forall(Set.empty, TyArrow (TyFloat, TyArrow (TyFloat, TyBool))))
    ("-", Forall(Set.empty,TyArrow (TyFloat, TyFloat)))

    // logical
    ("and",Forall(Set.empty,TyArrow (TyBool, TyArrow (TyBool, TyBool))))
    ("or", Forall(Set.empty,TyArrow (TyBool, TyArrow (TyBool, TyBool))))
    ("not",Forall(Set.empty,TyArrow (TyBool, TyBool)))
]

let type_error fmt = throw_formatted TypeError fmt

type subst = (tyvar * ty) list
   
// fresh variable generator
let mutable fresh_tyvar_counter = 0
let generate_fresh_tyvar () : ty =
    fresh_tyvar_counter <- fresh_tyvar_counter + 1
    TyVar fresh_tyvar_counter


// applies a substitution to a type, returning the new type 
let rec apply_subst (s : subst) (t : ty) : ty = 
    match t with
    | TyName _ -> t

    | TyVar tv -> 
        try
            let _, t1 = List.find (fun (tv1, _) -> tv1 = tv) s 
            in 
                t1
        with KeyNotFoundException -> t

    | TyArrow (t1, t2) -> TyArrow (apply_subst s t1, apply_subst s t2)

    | TyTuple ts -> 
        TyTuple (List.map (apply_subst s) ts)

// applies a substitution to a type scheme, returning the new type scheme
let apply_subst_scheme s (Forall (tvs, t)) = 
    Forall (tvs, apply_subst (List.filter (fun (tv, _) -> not (Set.contains tv tvs)) s) t)

// applies a substitution to the environment, returning the new environment
let apply_subst_env sub env =
    List.map (fun (id, schema) -> (id, apply_subst_scheme sub schema)) env

// composes two substitutions
let compose_subst sub1 sub2 = 
    let sub2 = List.map (fun (x, t) -> (x, apply_subst sub1 t)) sub2
    sub1 @ sub2



// checks if type variable tv2 occurs in type t1
let rec occurs (tv2: tyvar) (t1 : ty) : bool =
    match t1 with
    | TyName _ -> false
    | TyVar tv1 -> tv1 = tv2
    | TyArrow (t1, t2) -> occurs tv2 t1 || occurs tv2 t2
    | TyTuple tt -> List.exists (fun t -> occurs tv2 t) tt


// ------------------------ UNIFICATION ------------------------
// Based on Martelli and Montanari's unification algorithm
let rec unify (t1 : ty) (t2 : ty) : subst = 
    match t1, t2 with
    | TyName n1, TyName n2 when n1 = n2 -> []

    | TyVar tv, _ -> if occurs tv t2 then 
                        type_error "unification error: variable %O occurs in %O" tv t2
                     else [(tv , t2)]

    | _ , TyVar tv -> if occurs tv t1 then
                        type_error "unification error: variable %O occurs in %O" t1 tv
                      else [(tv , t1)]

    | TyArrow (tl1, tr1), TyArrow (tl2, tr2) -> 
        let sub = unify tl1 tl2
        compose_subst (unify (apply_subst sub tr1) (apply_subst sub tr2)) sub

    | TyTuple ts1, TyTuple ts2 when List.length ts1 = List.length ts2 ->
        List.fold (fun s (t1, t2) -> compose_subst (unify (apply_subst s t1) (apply_subst s t2)) s) [] (List.zip ts1 ts2)

    | _ -> type_error "unification error: %O and %O cannot be unified" t1 t2


// returns the free variables in a type
let rec freevars_ty (t : ty) =
    match t with
    | TyName _ -> Set.empty
    | TyVar tv -> Set.singleton tv
    | TyArrow (t1, t2) -> (freevars_ty t1) + (freevars_ty t2)
    | TyTuple ts -> List.fold (fun r t -> r + freevars_ty t) Set.empty ts

let freevars_scheme (Forall (tvs, t)) = freevars_ty t - tvs

// returns the free variables in a scheme env
let freevars_scheme_env (env: scheme env) =
    List.fold (fun r (_, sch) -> r + freevars_scheme sch) Set.empty env

// generalizes a type into a type scheme
let generalization (t : ty) (env: scheme env) : scheme =
    let tvs = freevars_ty t - freevars_scheme_env env
    Forall(tvs, t)


// instantiates a type scheme into a type, refreshing its polymorphic type variables
let instantiate (Forall (tvs, t)) : ty = 
    let sub = List.map (fun tv -> (tv, generate_fresh_tyvar())) (Set.toList tvs)
    apply_subst sub t

// ------------------------ TYPE INFERENCE ------------------------
let rec typeinfer_expr (env : scheme env) (e : expr) : ty * subst =
    match e with
    | Lit (LInt _) -> TyInt, [] 
    | Lit (LBool _) -> TyBool, []
    | Lit (LFloat _) -> TyFloat, [] 
    | Lit (LString _) -> TyString, []
    | Lit (LChar _) -> TyChar, [] 
    | Lit LUnit -> TyUnit, []

    | Var x -> 
        let res = List.tryFind (fun (y, _) -> x = y) env
        match res with
        | None -> type_error "type inference error: variable %O is undefined" x
        | Some (_, scheme) -> (instantiate scheme, [])

    | Lambda (x, tyo, e) -> 
        let fresh_tyvar = generate_fresh_tyvar ()
        let env = (x, Forall(Set.empty, fresh_tyvar)) :: env
        let (t2, sub1) = typeinfer_expr env e
        let t1 = apply_subst sub1 fresh_tyvar

        let subo =
            match tyo with
            | None -> []
            | Some t -> unify t1 t

        (TyArrow(t1, t2), compose_subst subo sub1)

    | App (e1, e2) ->
        let (t1, sub1) = typeinfer_expr env e1
        let (t2, sub2) = typeinfer_expr (apply_subst_env sub1 env) e2 
        let fresh_tyvar = generate_fresh_tyvar ()
        let sub3 = unify (apply_subst sub2 t1) (TyArrow (t2, fresh_tyvar))
        let t3 = apply_subst sub3 fresh_tyvar
        let sub4 = compose_subst sub3 (compose_subst sub2 sub1)

        (t3, sub4)

    | Let (x, tyo, e1, e2) ->
        let (t1, sub1) = typeinfer_expr env e1

        let subo = 
            match tyo with
            | None -> []
            | Some t -> unify t1 t

        let sub1o = compose_subst subo sub1 
        let sch1 = generalization (apply_subst sub1o t1) (apply_subst_env sub1o env)
        let (t2, sub2) = typeinfer_expr ((x, sch1) :: apply_subst_env sub1o env) e2
        let sub3 = compose_subst sub2 sub1

        (t2, sub3)

    | LetRec (f, tfo, e1, e2) ->
        let fresh_tyvar = generate_fresh_tyvar ()
        let fresh_schema = Forall (Set.empty, fresh_tyvar)
        let (t1, sub1) = typeinfer_expr ((f, fresh_schema) :: env) e1
        let subu = unify t1 (apply_subst sub1 fresh_tyvar)

        let subo =
            match tfo with
            | None -> []
            | Some t -> unify (apply_subst subu t1) t

        let sub1o = compose_subst subo (compose_subst subu sub1) 
        let sch1 = generalization (apply_subst sub1o t1) (apply_subst_env sub1o env)
        let (t2, sub2) = typeinfer_expr ((f, sch1) :: apply_subst_env sub1o env) e2
        let sub3 = compose_subst sub2 sub1o

        (t2, sub3)

    | IfThenElse (e1, e2, e3o) ->
        let (t1, sub1) = typeinfer_expr env e1
        let sub2 = unify t1 TyBool
        let sub3 = compose_subst sub2 sub1
        let (t2, sub4) = typeinfer_expr (apply_subst_env sub3 env) e2
        let sub5 = compose_subst sub4 sub3
        let (t3, sub6) = 
            match e3o with
            | Some e3 -> typeinfer_expr (apply_subst_env sub5 env) e3
            | None -> (TyUnit, sub5)
        let sub7 = compose_subst sub6 sub5
        let sub8 = unify (apply_subst sub7 t2) (apply_subst sub7 t3)
        let t = apply_subst sub8 t2
        let sub9 = compose_subst sub8 sub7

        (t, sub9)

    | Tuple es ->
        let f (ts, sub) exp = 
            let (ti, subi) = typeinfer_expr (apply_subst_env sub env) exp
            (ts @ [ti], compose_subst subi sub)

        let ts, sub = List.fold f ([], []) es

        (TyTuple (List.map (apply_subst sub) ts), sub)


    | BinOp (e1, op, e2) ->
        if List.contains op (List.map (fun(s, _) -> s) gamma0)
            then
                typeinfer_expr env (App (App (Var op, e1), e2))
            else
                unexpected_error "type inference error: binary operator (%s) is not supported" op

    | UnOp (op, e) ->
        if List.contains op (List.map (fun(s, _) -> s) gamma0)
            then
                typeinfer_expr env (App (Var op, e))
            else
                unexpected_error "type inference error: unary operator (%s) is not supported" op

    | _ -> failwithf "type inference error: this expression is not supported"



// ------------------------ TYPE CHECKER ------------------------
let rec typecheck_expr (env : ty env) (e : expr) : ty =
    match e with
    | Lit (LInt _) -> TyInt
    | Lit (LFloat _) -> TyFloat
    | Lit (LString _) -> TyString
    | Lit (LChar _) -> TyChar
    | Lit (LBool _) -> TyBool
    | Lit LUnit -> TyUnit

    | Var x ->
        let _, t = List.find (fun (y, _) -> x = y) env
        t

    | Lambda (x, None, e) -> unexpected_error "typecheck_expr: unannotated lambda is not supported"
    
    | Lambda (x, Some t1, e) ->
        let t2 = typecheck_expr ((x, t1) :: env) e
        TyArrow (t1, t2)

    | App (e1, e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1 with
        | TyArrow (l, r) ->
            if l = t2 then r 
            else type_error "wrong application: argument type %s does not match function domain %s" (pretty_ty t2) (pretty_ty l)
        | _ -> type_error "expecting a function on left side of application, but got %s" (pretty_ty t1)

    | Let (x, tyo, e1, e2) ->
        let t1 = typecheck_expr env e1
        match tyo with
        | None -> ()
        | Some t -> if t <> t1 then type_error "type annotation in let binding of %s is wrong: exptected %s, but got %s" x (pretty_ty t) (pretty_ty t1)
        typecheck_expr ((x, t1) :: env) e2

    | LetRec (f, None, e1, e2) ->
        unexpected_error "typecheck_expr: unannotated let rec is not supported"
        
    | LetRec (f, Some tf, e1, e2) ->
        let env0 = (f, tf) :: env
        let t1 = typecheck_expr env0 e1
        match t1 with
        | TyArrow _ -> ()
        | _ -> type_error "let rec is restricted to functions, but got type %s" (pretty_ty t1)
        if t1 <> tf then type_error "let rec type mismatch: expected %s, but got %s" (pretty_ty tf) (pretty_ty t1)
        typecheck_expr env0 e2

    | IfThenElse (e1, e2, e3o) ->
        let t1 = typecheck_expr env e1
        if t1 <> TyBool then type_error "if condition must be a bool, but got a %s" (pretty_ty t1)
        let t2 = typecheck_expr env e2
        match e3o with
        | None ->
            if t2 <> TyUnit then type_error "if-then without else requires unit type on then branch, but got %s" (pretty_ty t2)
            TyUnit
        | Some e3 ->
            let t3 = typecheck_expr env e3
            if t2 <> t3 then type_error "type mismatch in if-then-else: then branch has type %s and is different from else branch type %s" (pretty_ty t2) (pretty_ty t3)
            t2

    | Tuple es ->
        TyTuple (List.map (typecheck_expr env) es)

    | BinOp (e1, ("+" | "-" | "/" | "%" | "*" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> TyInt
        | TyFloat, TyFloat -> TyFloat
        | TyInt, TyFloat
        | TyFloat, TyInt -> TyFloat
        | _ -> type_error "binary operator expects two int operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        
    | BinOp (e1, ("<" | "<=" | ">" | ">=" | "=" | "<>" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyInt, TyInt -> ()
        | _ -> type_error "binary operator expects two numeric operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (e1, ("and" | "or" as op), e2) ->
        let t1 = typecheck_expr env e1
        let t2 = typecheck_expr env e2
        match t1, t2 with
        | TyBool, TyBool -> ()
        | _ -> type_error "binary operator expects two bools operands, but got %s %s %s" (pretty_ty t1) op (pretty_ty t2)
        TyBool

    | BinOp (_, op, _) -> unexpected_error "typecheck_expr: unsupported binary operator (%s)" op

    | UnOp ("not", e) ->
        let t = typecheck_expr env e
        if t <> TyBool then type_error "unary not expects a bool operand, but got %s" (pretty_ty t)
        TyBool
            
    | UnOp ("-", e) ->
        let t = typecheck_expr env e
        match t with
        | TyInt -> TyInt
        | TyFloat -> TyFloat
        | _ -> type_error "unary negation expects a numeric operand, but got %s" (pretty_ty t)

    | UnOp (op, _) -> unexpected_error "typecheck_expr: unsupported unary operator (%s)" op

    | _ -> unexpected_error "typecheck_expr: unsupported expression: %s [AST: %A]" (pretty_expr e) e
