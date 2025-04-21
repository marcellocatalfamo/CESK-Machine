(*part 1: definitions:*)
type var = string

(*WE USED TERMS (T) INSTEAD OF EXPRESSIONS (E)*)
type term =
| Var of var
| App of term * term
| Lam of var * term (*Post presentation: thats for immutable vars*)
| Sig of var * term (*Post presentation: thats for mutable vars*)
(*Post presentation: extend from the lambda calculus to do concrete stuff*)
| Int of int
| Add of term * term
| Mult of term * term
| IfZero of term * term * term  (* Didn't want to add bools so like in C if the condition evaluates to 0 then true else false *)
| Fix of term

module TermMap = Map.Make(struct type t = int let compare = compare end)

type types = (*could be used to typecheck programs!*)
| Integer
| Fun of types * types

(*in my head, this will be very basic: start at address 0, everytime we want a new address,
just add one and keep in store which address we're at: no deletion implemented yet*)
type address = int

type register = (string * value ref)
and registers = register list

and bytecode =
|GEN (*Generate value*)
|LOD (*Load value*)
|LFE (*Load from environment*)
|MTE (*Move to environment*)
|PVR (*Place value in register*)
|AVR (*Add value to register*)
|MVR (*Multiply value in register*)
|MOV (*Move value from register into register*)
|LAR (*Load address in register*)
|SAR (*Store address to register*)
|CNA (*Create new address*)
|CNI (*Create new index*)
|IUE (*If unfound, error*)
|SEV (*Set environment size*)
|LUA (*Look up address*)
|BEZ (*Branch if equal to zero*)
|Label of int (*Label for branching*)
|END (*Terminate program*)

and ins = 
|Value of bytecode * value (*GEN*)
|Arith of bytecode * register * int (*PVR, AVR, MVR*)
|Mov of bytecode * register * register (*MOV*)
|Env of bytecode * register * register (*LFE, MFE*)
|Mem of bytecode * register * register (*LAR, SAR*)
|Unary of bytecode * register (*CNA, IUE, SEV*)
|Branch of bytecode * register * int
|LabelBC of bytecode
|Jump of bytecode
|Pseudo of bytecode * register * var (*LUA*)
|Halt of bytecode

and program = ins list

and value = 
| CloLam of env * var * term
| CloSig of env * var * term
| ByteCloLam of env * var * program
| ByteCloSig of env * var * program
| IntVal of int
and env_value = (*need this now since our environment either maps to a value or address*)
  | EnvVal of value   (*immutable vars*)
  | EnvAddr of address     (* like before --> mutable vars *)
and env = (string * env_value) list


type store = value option TermMap.t

(*Part2: Implementing eval directly*)

(*HELPER METHODS*)

(*need ways to access the store first*)
  (*Find the value that is mapped at that addoress*)
let lookup_store (st : store) (a : address) : value =
  match TermMap.find_opt a st with
  | None -> failwith ("No entry in store for address " ^ string_of_int a)
  | Some None -> failwith ("Address " ^ string_of_int a ^ " is allocated but empty")
  | Some (Some v) -> v
(*The above method WILL BE PRIVATE conceptually. IE the store will only be accessed by helper methods in the env*)

(*Find the value that is mapped to that variable*)
let rec lookup_env (r : env) (x : var) (st: store): value =
  match r with
  | [] -> failwith ("Unbound variable " ^ x)
  | (x', v)::rs ->
      if x' = x then 
        (match v with 
          | EnvVal v -> v
          | EnvAddr a -> lookup_store st a ) (*so the store will only be accessed from this helper*)
      else lookup_env rs x st



(*Again the 4 methods below in theory are private too*)
let addOrUpdate_store (st : store) (a : address) (v : value) : store =
  TermMap.add a (Some v) st

(*global counter as seen in 302*)
(*generate the next store address that's empty*)
let fresh_address =
  let counter = ref 0 in
  fun () ->
    let a = !counter in
    incr counter;
    a

(*Basically a deBruijn index*)
let index (t : bool) (n : int) =
  let counter = ref 0 in
  let fresh_index = 
  fun () ->
    let a = !counter in
    incr counter;
    a
  in let set_index = fun () -> counter := n + 1; n in
  if t then fresh_index () else set_index ()

let fresh_label =
  let counter = ref 0 in
  fun () ->
    let a = !counter in
    incr counter;
    a

  
(*THIS HANDLES ALL THE CASES *)
(*1. a new immutable variable --> only update the environment*)
let add_immutable_env (r : env) (x : var) (v : value) : env =
  (x, EnvVal v) :: r



(*2. a new mutable variable --> update both with the new address
3. an existing mutable variable --> only update te store *)
(*I combine both 2 and 3 in one so that when using a sigma abstraction if x already exists there wont be a new binding that will be added by default: the store will simply be updated --> this is what I call mutability*)
(*In all honnesty, was struggling so much with doing these 2 simultaneously that I ended up getting it from Chat GPT*)
let addOrUpdate_mutable (r : env) (x : var) (v : value) (st : store) : env * store =
  try
    match List.assoc x r with
    | EnvVal _ ->
        failwith ("Cannot mutate immutable variable " ^ x)
    | EnvAddr a ->
        let st' = addOrUpdate_store st a v in
        (r, st')
  with Not_found ->
    (* Add new mutable binding *)
    let a = fresh_address () in
    let st' = addOrUpdate_store st a v in
    ((x, EnvAddr a) :: r, st')
        


(*-------------------------------------------------VERSION 1-----------------------------------------------------*)
    (*direct*)

(*the reason I am passing the store back as output unlike the env is because I want to keep the store immutable:
 each call consumes an old store and produces a new one *)
let rec eval_direct (st : store) (r : env) (t : term) : (value * store) = 
  match t with
   (*store remains unchanged, almost like in class but need to get address first then value*)
  | Var x -> let v = lookup_env r x st in (v, st)
  (*store remains unchanged: and this case is like the one saw in class*)
  | Lam(x, t') -> (CloLam(r, x, t'), st)
  | Sig(x, t') -> (CloSig(r, x, t'), st)
  | App(t1, t2) ->
    (*like in class, first check t1 ends up being a closure (ie a lam)*)
    (match eval_direct st r t1 with 
    |  (CloLam(r', x, t), st1)  ->
      (*like in class evaluate t2*)
      let (v, st2) = eval_direct st1 r t2 in
      (*& extend the store accordingly*)
      eval_direct st2 (add_immutable_env (r') (x) (v)) t

      | (CloSig(r', x, t), st1) ->
        (*like in class evaluate t2*)
          let (v, st2) = eval_direct st1 r t2 in
          (*now update according to if its a new or existing variable the store/env*)
          let (r'', st3) = addOrUpdate_mutable r' x v st2 in
          eval_direct st3 r'' t

      | _ -> failwith "t1 needs to evaluate to a closure in applications!"
    )

    | Int n  ->(IntVal n, st)

    | Add(t1,t2) ->
      let (v1, st1) = eval_direct st r t1 in
      let (v2, st2) = eval_direct st1 r t2 in (*use the store we got AFTER evaling t1*)
      (match (v1, v2) with
        | (IntVal int1, IntVal int2) -> (IntVal(int1+int2), st2) 
        | _ -> failwith "both arguments of Add need to evaluate to integers!")
    | Mult(t1,t2) -> (*just like add*)
      let (v1, st1) = eval_direct st r t1 in
      let (v2, st2) = eval_direct st1 r t2 in 
      (match (v1, v2) with
        | (IntVal int1, IntVal int2) -> (IntVal(int1*int2), st2) 
        | _ -> failwith "both arguments of Mult need to evaluate to integers!")
    
    | IfZero(t, t1, t2) ->
        let (v, st1) = eval_direct st r t in
        (match v with
         | IntVal 0 -> eval_direct st1 r t1
         | IntVal _ -> eval_direct st1 r t2
         | _ -> failwith "The condition of the if statement needs to evaluate to an integer!"
        )
    
    | Fix t ->
    (* 1) Evaluate the function term to a closure *)
    let (vf, st1) = eval_direct st r t in

    (match vf with
      | CloLam (r_clo, x, body) ->
          (* 2) Allocate exactly one address for “f” *)
          let a  = fresh_address () in
          (* 3) Bind x ↦ Addr a in the closure’s env *)
          let r' = (x, EnvAddr a) :: r_clo in

          (* 4) Evaluate the body under that env, threading the store *)
          let (v_body, st2) = eval_direct st1 r' body in

          (* 5) Store the result at *that same* address a *)
          let st3 = addOrUpdate_store st2 a v_body in

          (* 6) And return *)
          (v_body, st3)

      | _ ->
          failwith "Fix: expected a CloLam closure"
      )
    


(*-------------------------------------------------VERSION 2-----------------------------------------------------*)


(*part3: converting to CPS*)
(*reminder: call the fn, and assume the output will be passed as input to k*)
let rec evalCPS (st : store) (r : env) (t : term) (k : value -> store -> 'gamma) : 'gamma =
  match t with
  (*var and lam case the same just pass in k*)
  | Var x -> k (lookup_env r x st) st
  | Lam(x, t') -> k (CloLam(r, x, t')) st
  | Sig(x, t') -> k (CloSig(r, x, t')) st
  (*same as the app case but for each eval call, we assume the output of that is going to be passed into the continuation*)
  | App(t1, t2) ->  evalCPS st r t1 (fun (v) (st1) -> (*A*)
      match v with
      | CloLam(r', x, t') -> 
        evalCPS st1 r t2 (fun v' st2 -> (*B*)
          let r'' = add_immutable_env r' x v' in
          evalCPS st2 (r'') t' k
        )
      | CloSig(r', x, t') ->
        evalCPS st1 r t2 (fun v' st2 -> (*B*)
          let (r'', st3) = addOrUpdate_mutable r' x v' st2 in
          evalCPS st3 (r'') t' k
        )
      | _ -> failwith  "t1 needs to evaluate to a closure in applications!"
      )
      
    | Int n -> k (IntVal n) st
    
    | Add(t1, t2) ->
          evalCPS st r t1 (fun v1 st1 -> (*C*)
            evalCPS st1 r t2 (fun v2 st2 -> (*D*)
              match (v1, v2) with
              | (IntVal int1, IntVal int2) -> k (IntVal (int1 + int2)) st2
              | _ -> failwith "both arguments of Add need to evaluate to integers!" )
          )
    | Mult(t1, t2) ->
          evalCPS st r t1 (fun v1 st1 -> (*E*)
            evalCPS st1 r t2 (fun v2 st2 -> (*F*)
              match (v1, v2) with
              | (IntVal int1, IntVal int2) -> k (IntVal (int1 * int2)) st2
              | _ -> failwith "both arguments of Mult need to evaluate to integers!")
          )
    
    | IfZero(t, t1, t2) ->
          evalCPS st r t (fun v st1 -> (*G*)
            match v with
            | IntVal 0 -> evalCPS st1 r t1 k
            | IntVal _ -> evalCPS st1 r t2 k
            | _ -> failwith "The condition of the if statement needs to evaluate to an integer!"
          )

    (*made by chat*)
    | Fix t ->
      evalCPS st r t (fun vf st1 -> (*H*)
        match vf with
        | CloLam(r_clo, x, body) ->
            (* Allocate a single cell `a` for `f` *)
            let a  = fresh_address () in
            let r' = (x, EnvAddr a) :: r_clo in

            (* Evaluate the body under the extended env `r'` *)
            evalCPS st1 r' body (fun v_body st2 -> (*J*)
              (* Store *into* that same address `a`! *)
              let st3 = addOrUpdate_store st2 a v_body in
              k v_body st3
            )

        | _ ->
            failwith "Fix: expected CloLam"
)


(*-------------------------------------------------VERSION 3-----------------------------------------------------*)


(*part4: defunctionalising*)

(*note, we need to specify for every time we call evalCPS inside a continuation, a new name for that behaviour*)
(*to simplify conversion, I have labelled then A->J*)
type cont =
| Halt
| Ar of env * term * cont (*A*)
| Ap of value * cont (*B*)
(*add and mult are like applications*)
| AddAr of env * term * cont (*C*) (*keep RHS left to evaluate with its environment*)
| AddAp of value * cont (*D*) (*when we evaluate RHS keep the LHS value to then use it later when applying*)
| MultAr of env * term * cont (*E*)
| MultAp of value * cont (*F*)
| IfAr of env * term * term * cont (*G*) (*we need to keep in store both branches depending on which one we select*)
(*no application case for ifs because once we evaluate condition branch we dont use it anymore*)
| FixAr   of cont                     (* H*)
| FixDone of address * cont           (* J*)

(*Part 5: Bytecode conversion*)

(*Program start*)

let get_fun funs vals final_vals : unit =
  match !funs with
  | (x, l) :: ls ->
    funs := ls;
    (*Once a term is done being evaluated, deposite the code that represents it in the list*)
    let v = List.assoc x !vals in 
    (match v with
      | ByteCloLam(r, x, _) -> final_vals := !final_vals @ [ByteCloLam(r, x, !l)]
      | ByteCloSig(r, x, _) -> final_vals := !final_vals @ [ByteCloSig(r, x, !l)]
      | _ -> failwith "Not a function!");
  | [] -> ()

and add_fun (x : var) (v : value) funs vals : unit =
   funs := (x, ref []) :: !funs;
   vals := (x, v) :: !vals

and build_funs (p : program) funs : unit = 
  funs := List.map(fun (x, l) -> (x, ref (p @ !l)) ) !funs

let emit (p : program ref) funs (l : program) : unit =
  build_funs l funs; p := !p @ l

let get_reg (rs : registers) (reg : string) : register =
    List.find (fun (name, _) -> reg = name) rs

let get_regs (regs: registers) (names : string list) : registers =
let rec get (regs: registers) (names : string list) (rs : registers) : registers =
    match names with
    |[] -> rs
    |n::ns -> get regs ns ((get_reg regs n)::rs)
in get regs names []

(*let free_space (h : store) (p : env) (p' : env) : store * address =
    let (i, j) = (List.length p, List.length p') in
    set_top i;
    (TermMap.mapi (fun k v -> 
      if (k >= i && j > k) then 
        None else v) h, i)*)

let get_values = 
  let fun_rec_list : (var * int) list ref = ref [] in
  let funs : (var * program ref) list ref = ref [] in
  let (vals, final_vals) : ((var * value) list ref * value list ref) = (ref [], ref []) in
  fun () -> (funs, vals, final_vals, fun_rec_list)

let code_gen (st : store) (r : env) (value : value) (k : cont) (rs : registers) (prog : program ref) : unit =
  let (funs, vals, final_vals, fun_rec_list) = get_values () in
  let fix_bindings : value list ref = ref [] in
  let emit' = emit prog funs in 
  let get_regs' = get_regs rs in
  
  match k with
   | Halt -> emit' [Halt(END)]

   | Ar(r, t2, k) | AddAr(r, t2, k) | MultAr(r, t2, k) | IfAr(r, _, t2, k) ->
    let [fp;sp;r1;v] = get_regs' ["fp";"sp";"r1";"v"] in
    get_fun funs vals final_vals;
    let l = [Unary(SEV, sp); Mov(MOV, sp, fp)] in emit' l 

   | Ap (CloLam(r, x, t), k) -> 
    let [fp;sp;r1;v] = get_regs' ["fp";"sp";"r1";"v"] in
    let vv = ByteCloLam(r, x, []) in
    add_fun x vv funs vals;
    let l = [Value(GEN, vv); Unary(CNI, fp); Mov(MOV, fp, sp); Env(MTE, v, r1)] in emit' l 

   | Ap (CloSig(r, x, t), k) -> 
    let [fp;sp;r1;v] = get_regs' ["fp";"sp";"r1";"v"] in
    let vv = ByteCloSig(r, x, []) in
    add_fun x vv funs vals;
    let l = [Value(GEN, vv); Unary(CNI, fp); Unary(CNA, r1);
            Mov(MOV, fp, sp); Env(MTE, r1, fp); Mem(SAR, v, r1)] in emit' l 

   | AddAp(IntVal int1, k) -> 
    let [v] = get_regs' ["v"] in
    let l = [Arith(AVR, v, int1)] in emit' l 

   | MultAp(IntVal int1, k) -> 
    let [v] = get_regs' ["v"] in
    let l = [Arith(MVR, v, int1)] in emit' l 
   
   | FixAr k2 ->
     (* v must be a function closure *)
    let [r1;fp;(_, v') as v] = get_regs' ["r1";"fp";"v"] in
    (match !v' with
    | ByteCloLam(_, x, _) ->
      let f = List.assoc_opt x !fun_rec_list in
      (match f with
      |Some a -> 
        let l = [Unary(CNI, fp); Unary(CNA, r1); Env(MTE, r1, fp); 
                Mem(SAR, v, r1); LabelBC(Label a)] in emit' l;
                let (_, r1') = r1 in
                fix_bindings := !r1' :: !fix_bindings
      |None -> failwith "Recursive call not defined!" )
    | _ -> failwith "Needs to be a function!")
 
   | FixDone (a, k2) ->
    (* Store the result into the reserved address, then continue *)
    let [sp;r1;v] = get_regs' ["r1";"v"] in
    (match !fix_bindings with
    | b :: bs -> 
      fix_bindings := bs;
      let l = [Value(LOD, b); Env(MTE, v, r1)] in emit' l 
    | _ -> failwith "Not in a recursive call")
  | _ -> failwith "Invalid argument types"

(*Back to part 4, with some additions for bytecode stuff*)

let rec eval (st : store) (r : env) (t : term) (k : cont) (rs : registers) (prog : program ref) : (value * store) =
  
  let eval' (st : store) (r : env) (t : term) (k : cont) : (value * store) = 
    eval st r t k rs prog in
  let (funs, vals, final_vals, fun_rec_list) = get_values () in
  let emit' = emit prog funs in 
  let get_regs' = get_regs rs in

  let apply' (st : store) (v : value) (k : cont) : (value * store) =
   apply st v k rs prog
  in 

  match t with
  | Var x ->
      let [v] = get_regs' ["v"] in
      let l = [Pseudo(LUA, v, x)] in emit' l;
      apply' st (lookup_env r x st) k
  | Lam(x, t') ->
      apply' st (CloLam(r, x, t')) k
  | Sig(x, t') ->
    apply' st (CloSig(r, x, t')) k
  | App(t1, t2) ->
      (* Evaluate t1 first and notify through Ar that t2 needs to be evaluated next*)
      eval' st r t1 (Ar(r, t2, k))
  | Int n ->  
      let [v] = get_regs' ["v"] in
      let l = [Arith(PVR, v, n)] in emit' l;
      apply' st (IntVal n) k
  | Add(t1,t2) ->
      eval' st r t1 (AddAr(r, t2, k))
  | Mult(t1,t2) ->
    eval' st r t1 (MultAr(r, t2, k))
  | IfZero(t, t1, t2) ->
    eval' st r t (IfAr(r, t1, t2, k))
  | Fix t -> 
    (* Generate a label to jump back to, and store which function this is in memory *)
    (match t with 
    | Lam(x, t') | Sig (x, t') ->
        let a = fresh_label () in
        fun_rec_list := (x, a) :: !fun_rec_list;
        eval' st r t (FixAr k)
    | _ -> failwith "Must fix an abstraction!")
and apply (st : store) (v : value) (k : cont) (rs : registers) (prog : program ref) : (value * store) =
  
  let (funs, vals, final_vals, _) = get_values () in
  let emit' = emit prog funs in 
  let get_regs' = get_regs rs in
  let eval' (st : store) (r : env) (t : term) (k : cont) : (value * store) = 
    code_gen st r v k rs prog;
    eval st r t k rs prog
  in

  let apply' (st : store) (v : value) (k : cont) : (value * store) =
    apply st v k rs prog
   in 

  match k with
  | Halt -> (v,st) (*this is the final state mentioned in class --> from theorem will always be reached!*)
  | Ar(r, t2, k) -> eval' st r t2 (Ap(v, k))
  | Ap (CloLam(r, x, t), k) -> 
    eval' st (add_immutable_env r x v) t k
  | Ap (CloSig(r, x, t), k) ->
    let (r', st') = addOrUpdate_mutable r x v st in (*so much cleaner with the helper*)
    eval' st' r' t k
  | AddAr(r, t2, k) -> eval' st r t2 (AddAp(v, k))
  | AddAp(IntVal int1, k) -> (match v with
    | IntVal int2 -> apply' st (IntVal(int1 + int2)) k
    | _ -> failwith "both arguments of Add need to evaluate to integers!")
  | MultAr(r, t2, k) -> eval' st r t2 (MultAp(v, k))
  | MultAp(IntVal int1, k) -> (match v with
    | IntVal int2 -> apply' st (IntVal(int1 * int2)) k
    | _ -> failwith "both arguments of Mult need to evaluate to integers!")
  | IfAr(r, t1, t2, k) -> 
    (*We need to do some bytecode splicing here*)
    let a = fresh_label () in
    let [vv] = get_regs'  ["v"] in
    emit' [Branch(BEZ, vv, a)];
    (match v with
    | IntVal 0 -> eval' st r t1 k
    | IntVal _ -> 
      emit' [LabelBC(Label a)];
      eval' st r t2 k
    | _ -> failwith "The condition of the if statement needs to evaluate to an integer!")
  
  | FixAr k2 ->
    (* v must be a function closure *)
    (match v with
      | CloLam(r_clo, x, body) ->
          let a  = fresh_address () in
          let r' = (x, EnvAddr a) :: r_clo in
          (* Evaluate body under the new env, continue in FixDone *)
          eval' st r' body (FixDone(a, k2))
      | _ ->
          failwith "Fix: expected a CloLam"
    )

  | FixDone (a, k2) ->
      (* Store the result into the reserved address, then continue *)
      let st' = addOrUpdate_store st a v in
      apply' st' v k2

  | _ -> failwith "Invalid argument types"


(*example given in class to run this version of eval*)
(*in class: eval' e = eval [] e (fun x -> x) but we defunctionalised it*)
let eval' (t:term) : value  =
  fst (eval TermMap.empty [] t (Halt) [] (ref [])) (*both store and env start up as empty*)

(*Creating these same helpers for the versions 1 and 2 of eval*)
let evalCPS' (t:term) : value =
  fst (evalCPS TermMap.empty [] t (fun v st -> (v, st))) (*as seen in class its the identity function*)

let eval_direct' (t:term) : value =
  fst (eval_direct TermMap.empty [] t) 


let eval_algorithms : (string * (term -> value)) list = [
  ("direct",  eval_direct');
  ("cps",     evalCPS');
  ("defunctionalised", eval')
]

(*EXAMPLE ALGORITHMS made by chat*)
let fact_recursive =
  Fix (Lam("f",
    Lam("x",
      IfZero(Var "x", Int 1,
        Mult(Var "x", App(Var "f", Add(Var "x", Int (-1))))
      )
    )
  ))
  

  let fact_iterative =
    Lam("n",
      App(
        Sig("acc",
          App(
            Fix (Lam("f",
              Lam("x",
                IfZero(Var "x",
                        Var "acc",
                        App(
                          Sig("acc", Mult(Var "acc", Var "x")),  (* just update the existing acc *)
                          App(Var "f", Add(Var "x", Int (-1)))
                        )
                )
              )
            )),
            Var "n"
          )
        ),
        Int 1
      )
    )


let fact_algorithms : (string * term) list = [
  ("recursive",  fact_recursive);
  ("iterative", fact_iterative);
]

(* Run all tests for n = 5 chat as well*)
let () =
  List.iter (fun (ev_name, ev_fn) ->
    List.iter (fun (algo_name, algo_term) ->
      let t = App(algo_term, Int 5) in
      match ev_fn t with
      | IntVal v ->
        print_endline (ev_name ^ "-" ^ algo_name ^ ": " ^ string_of_int v)
      | _ ->
        print_endline (ev_name ^ "-" ^ algo_name ^ ": WRONG OUTPUT ")
    ) fact_algorithms
  ) eval_algorithms

  
let init (size : int) : env * store =
  let heap = TermMap.empty in
  let rec store_init = function
  |0 -> TermMap.add 0 None heap;
  |n -> TermMap.add n None (store_init (n - 1))
in ([], heap)

let compile (t : term) (size : int) : (value * program * value list) =
  let (env, store) = init size in
  let p : program ref = ref [] in
  let regs = [("fp", ref EnvAddr 0);("sp", ref EnvAddr 0); ("r1", ref EnvAddr 0); ("v", ref EnvAddr 0)] in
  let (v, _) = eval store [] t (Halt) regs p in
  let (_, _, l, _) = get_values in
  (v, !p, !l)
