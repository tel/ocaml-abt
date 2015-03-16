
(** Abstract binding trees.

    Original design is taken from the homework assignment here
    http://www.cs.cmu.edu/~rjsimmon/15312-s14/hws/hw1update2-handout.pdf

    Design also inspired by Neel Krishnaswami's design at
    http://semantic-domain.blogspot.com/2015/03/abstract-binding-trees.html

    The standard formalization is due to Robert Harper in PFPL. The original
    inspiration comes from Per Martin-Lof's "Method of Arities"
    http://www.cse.chalmers.se/research/group/logic/book/book.pdf

*)

module type Variable = sig
  type t
  val fresh : string -> t
  val equal : t -> t -> bool
  val compare : t -> t -> int
  val to_string : t -> string
  val to_user_string : t -> string
end

module Var : Variable = struct
  type t = string * int
  let counter = ref 0
  let fresh n = (n, (counter := !counter + 1; !counter))
  let equal (_, id1) (_, id2) = id1 = id2
  let compare (_, id1) (_, id2) = id2 - id1
  let to_string (s, n) = s ^ "@" ^ string_of_int n
  let to_user_string (s, _) = s
end

module type Operator = sig
  type t
  val arity : t -> int list
  val equal : t -> t -> bool
  val to_string : t -> string
end

module type Abt = sig
  module Variable : Variable
  module Operator : Operator

  type t

  type 'a view =
    | V of Variable.t
    | L of Variable.t * 'a
    | A of Operator.t * 'a list

  exception Malformed

  val into : t view -> t
  val out  : t -> t view

  val aequiv : t -> t -> bool
  val map : ('a -> 'b) -> ('a view -> 'b view)
end

module type AbtUtil = sig
  include Abt

  val freevars : t -> Variable.t list
  val subst : t -> Variable.t -> t -> t

  val var : Variable.t -> t
  val lam : Variable.t * t -> t
  val ($) : Operator.t -> t list -> t

  val to_string : t -> string
end

module Abt (V : Variable) (O : Operator) : Abt
  with type Variable.t = V.t
   and type Operator.t = O.t =
struct
  module Variable = V
  module Operator = O

  type 'a view =
    | V of Variable.t
    | L of Variable.t * 'a
    | A of Operator.t * 'a list

  type t =
    | Free of Variable.t
    | Bound of int
    | Lambda of t
    | Operator of Operator.t * t list

  exception Malformed

  let rec map_variables
      (free  : int -> Variable.t -> t)
      (bound : int -> int -> t)
      (tm : t)
    : t
    = let rec aux l tm = match tm with
      | Free v -> free l v
      | Bound n -> bound l n
      | Lambda t -> Lambda (aux (l+1) t)
      | Operator (o, ts) -> Operator (o, List.map (aux l) ts)
    in aux 0 tm

  let bind (v : Variable.t) (tm : t) : t =
    let free n v' = if Variable.equal v v' then Bound n else Free v' in
    let bound n m = Bound m in
    Lambda (map_variables free bound tm)

  (** Invariant, this is a term just underneath a lambda binder *)
  let unbind (tm : t) : Variable.t * t =
    let v = Variable.fresh "x" in
    let free n v' = if Variable.equal v v' then raise Malformed else Free v' in
    let bound _ m = if m = 0 then Free v else Bound m in
    (v, map_variables free bound tm)

  let into = function
    | V v -> Free v
    | L (v, tm) -> bind v tm
    | A (op, args) ->
      if (List.length (Operator.arity op) = List.length args)
      then Operator (op, args)
      else raise Malformed

  let out = function
    | Free v -> V v
    | Bound _ -> raise Malformed
    | Lambda tm -> let (var, tm') = unbind tm in L (var, tm')
    | Operator (op, args) -> A (op, args)

  let rec aequiv x y = match x, y with
    | Free vx            , Free vy            -> V.equal vx vy
    | Bound nx           , Bound ny           -> nx = ny
    | Lambda tx          , Lambda ty          -> aequiv tx ty
    | Operator (ox, axs) , Operator (oy, ays) ->
      Operator.equal ox oy && List.for_all2 aequiv axs ays
    | _                  , _                  -> false

  let map f = function
    | V v -> V v
    | L (v, a)  -> L (v, f a)
    | A (o, al) -> A (o, List.map f al)

end

module type Abt_Util = sig
  include Abt

  val freevars : t -> Variable.t list
  val subst : t -> Variable.t -> t -> t

  val var  : Variable.t -> t
  val lam  : Variable.t * t -> t
  val ($$) : Operator.t -> t list -> t
end

module Abt_Util (A : Abt) = struct
  include A

  let var v        = into (V v)
  let lam (v, e)   = into (L (v, e))
  let ($$) op args = into (A (op, args))

  let rec subst tm var exp =
    match out exp with
    | V v -> if Variable.equal var v then tm else exp
    | L (v, exp') -> lam (v, subst tm var exp')
    | A (op, args) -> op $$ List.map (subst tm var) args

  module VarSet : Set.S with type elt := Variable.t
    = Set.Make(Variable)

  let freevars exp =
    let rec aux exp =
      match out exp with
      | V v          -> VarSet.singleton v
      | L (v, exp')  -> VarSet.remove v (aux exp')
      | A (op, exps) -> List.fold_left VarSet.union VarSet.empty (List.map aux exps)
    in VarSet.elements (aux exp)

end

module TermOps = struct

  type t = Num of int | Str of string | Plus | Times | Cat | Len | Let

  let arity = function
    | Num n -> []
    | Str s -> []
    | Plus  -> [0; 0]
    | Times -> [0; 0]
    | Cat   -> [0; 0]
    | Len   -> [0]
    | Let   -> [0; 1]

  let equal a b = match a, b with
    | Num n, Num m -> n = m
    | Str s, Str t -> s = t
    | Plus , Plus  -> true
    | Times, Times -> true
    | Cat  , Cat   -> true
    | Len  , Len   -> true
    | Let  , Let   -> true
    | _    , _     -> false

  let to_string = function
    | Num n -> string_of_int n
    | Str s -> "\""^s^"\""
    | Plus  -> "plus"
    | Times -> "times"
    | Cat   -> "cat"
    | Len   -> "len"
    | Let   -> "let"

end

module Term = Abt_Util(Abt(Var) (TermOps))
