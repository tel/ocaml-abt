
module type Variable = sig
  type t
  val equal : t -> t -> bool
  val fresh : unit -> t
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
  exception NotImplemented

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
  
  let bind (tm : t) (v : Variable.t) : t =
    let free n v' = if V.equal v v' then Bound n else Free v' in
    let bound n m = Bound m in
    Lambda (map_variables free bound tm)

  let unbind (tm0 : t) : Variable.t * t =
    match tm0 with
    | Lambda tm ->
      let v = V.fresh () in
      let free n v' = if V.equal v v' then raise Malformed else Free v' in
      let bound _ m = if m = 0 then Free v else Bound m in
      (v, map_variables free bound tm)
    | _ -> raise Malformed
  
  let into x = raise NotImplemented
      
  let out x = raise NotImplemented
      
  let rec aequiv x y = match x, y with
    | Free vx            , Free vy            -> V.equal vx vy
    | Bound nx           , Bound ny           -> nx = ny
    | Lambda tx          , Lambda ty          -> aequiv tx ty
    | Operator (ox, axs) , Operator (oy, ays) ->
      O.equal ox oy && List.for_all2 aequiv axs ays
    | _                  , _                  -> false
      
  let map f = function
    | V v -> V v
    | L (v, a)  -> L (v, f a)
    | A (o, al) -> A (o, List.map f al)
            
end
