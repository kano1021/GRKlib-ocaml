module Make (Func : Fode.S) (Op : Sets.S) = struct
  module FuncInterval = Func(Interval)
  module F = Fadbad.F(Op)
  module T = Fadbad.T(Op)
  module FuncT = Func(T)
  module FuncF = Func(F)
  module TM = TaylorModel.Make(Op)

  (*parametres*)
  let h = ref 1e-4
  let order = ref 5

  let func_ex y =
    let open F in
    let z= sqrt y in 
    sqrt z

  let set_h hp =
    h := hp

  let set_order o =
    order := o

  let rk4_step f y = 
    let open F in
    let z= sqrt y in  
    1.5 *. z

  let real_rk4 f y_0 h =
    let k1 = f y_0 in
    let kk1 = y_0 +. h /. 2. *. k1 in
    let k2 = f kk1 in
    let kk2 = y_0 +. h /. 2. *. k2 in
    let k3 = f kk2 in 
    let kk3 = y_0 +. h *. k2 in
    let k4 = f kk3 in
    y_0 +. h /. 6. *. (k1 +. k2 +. k3 +. k4) 

  let compute_r f y_0 h =
    let ystar = real_rk4 f y_0 h in
    let r0 = yn + ystar in
    let r1 = f r0 in
    let rec aux r rp1 =
      if subset rp1 r then rp1
      else 
        let newrp1 = f rp1 in
        aux rp1 newrp1
    in 
    aux r0 r1

  let picard_integrate f y0 h =
    let ystar = real_rk4 f y_0 h in
    let r = compute_r f y_0 h in
    let fr = f r in
    let a = h * fr in
    () = y0 + a
 
  (* i'm not sure how to write this part, i'm trying to write a module for deriv once and then use it recursively but i failed *)

  module DFunc (Func : S) (Op : Fadbad.OpS) =
    struct
    let exec y =
      let open F in
      let y = lift y in
      let f = FuncF.exec y in
      let () = diff f 0 1 in
      let () = compute f in
      {
        value = value f;
        dx = deriv x 0;
        dy = deriv y 0;
      }
  end

  let jacobian_matrix f =
    let o = 0 in
        let aux 

 (* let jac_y f y = *)
  
  let add s1 s2 =
    let open Interval in
    Array.map2 (fun i1 i2 -> i1 + i2) s1 s2

  let add_margin s m =
    let open Interval in
    let margin  = make_bounds (-.m) m in
    Array.map (fun i -> i + margin) s

  let dilate s a =
    let open Interval in
    Array.map
      (fun i ->
        let rad = radius i in
        let margin = make_bounds (-.rad) rad in
        let margin = scale margin a in
        i + margin)
      s

  let compute_enclosure s0 t0 =
    let s0 = Array.map
               (fun s ->
                 let min,max = Op.get_min_max s in
                 Interval.make_bounds min max)
               s0
    in
    let deltaT = Interval.make_bounds 0. !dt in
    let compute_next enc =
      add s0 (scale (FuncInterval.exec enc deltaT) deltaT)
    in
    let rec find_fix_point enc next =
      if for_all2 Interval.subset next enc then
        next
      else
        let enc = dilate enc dilation in
        let next = compute_next enc in
        find_fix_point enc next
    in
    let enc = add_margin s0 0.1 in (* ensure no punctual state *)
    let next_enc = compute_next enc in
    find_fix_point enc next_enc

  let compute_expansion s0 t0 order =
    let x = Array.map (fun s -> T.lift s) s0 in
    let xp = FuncT.exec x t0 in
    let dim = Array.length x in
    (* eval all dimensions and store result in [r] *)
    let rec aux_dim r order d =
      if d >= dim then
        r
      else
        let _ = T.eval xp.(d) order in
        let () =
          T.set
            x.(d)
            (order+1)
            (Op.scale (T.deriv xp.(d) order) (1. /. (float (order + 1))))
        in
        let () = Array.set r d (T.deriv x.(d) (order+1)) in
        aux_dim r order (d+1)
    in
    (* eval all order and store expansion in [r] *)
    let rec aux_order r o =
      if o > order then
        r
      else
        let alpha = Array.make dim (Op.zero ()) in
        let alpha = aux_dim alpha o 0 in
        aux_order (alpha::r) (o+1)
    in
    aux_order [s0] 0

  let step s0 t0 : TM.t =
    let t0T = T.lift t0 in
    let enc = compute_enclosure s0 t0T in
    (* Taylor model coefficients *)
    let coef = compute_expansion s0 t0T (!order-1) in
    (* Taylor model remainder *)
    let enc = Array.map
                (fun i ->
                  let min, max = Interval.get_min_max i in
                  Op.make_bounds min max)
                enc
    in
    let enc_coef = compute_expansion enc t0T !order in
    let remainder =
      match enc_coef with
      | [] -> assert false
      | h::_ -> h
    in
    let coef = remainder :: coef in
    {
      dim = Array.length s0;
      coef;
      t0;
      dt_max = Op.make_float !dt;
    }

  (* return list of Taylor models at each step *)
  let integrate s0 t0 tEnd =
    let dtOp = Op.make_float !dt in
    let rec aux r s t =
      if t > tEnd then
        r
      else
        let () = Printf.fprintf Stdlib.stderr "time: %s\n%!" (string_of_float t) in
        let tm = step s (Op.make_float t) in
        (* let () = print_endline (string_of_int (List.length tm.coef)) in *)
        let next_s = TM.eval tm dtOp in
        let next_t = t +. !dt in
        aux (tm :: r) next_s next_t
    in
    aux [] s0 t0

  
   
  let k = ref 1.

  let set_k kp =
    k := kp

  let k1 = 0.2 /. !k
  let kp = 0.3 /. !k

  let compute_h h phi theta rtol=
    let phip = abs phip in
    let h5 = h ** 5 in
    let a = theta *. rtol /. phip /. h5 in
      a ** 0.2 *. h

  (* in this part i have problem with the definition of y_n+1, if it is integration by taylor method? *)
  let step_control f y_0 h err theta atol rtol =
    let yv0 = around y_0 err in 
    let yreal = real_rk4 f y_0 h in
    let ystar = real_rk4 f yv0 h in
    let ytilde = picard_integrate f y_0 h in
    let yv = around yreal err in
    let yjac = jac_y f y_0 in 
    let y = ingegrate y_0 0. h in
    let errmethod = yv -. ystar  in
    let errpropa = ystar -. yreal in
    let errround = yreal -. y in
    let phi = df5 y_0 in
    let hnew = compute_h h phi theta rtol in
    let rec aux h errm errr theta rtol =
        if errm < atol 
          then if errr < atol 
            then 
              h
        else else
          let theta_new = theta /. 2. in
          let hp = compute_h h theta_new rtol in
          aux hp errm errr theta_new rtol
    in
    aux h errm errr theta rtol

  
  

          


