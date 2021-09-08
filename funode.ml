module type S=
    functor (Op : Fadbad.OpS with type scalar = float) ->
    sig 
        val exec: Op.t array -> Op.t -> Op.t array
    end