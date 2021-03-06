(* Ant Colony Optimization - ACO*)
(* default commandline args *)
let num_points = ref 20
let num_iter = ref 500
let evap_rate_ref = ref 0.1
let beta_ref = ref 2.0
let exp_threshold_ref = ref 0.3

let usage = "usage: " ^ Sys.argv.(0) ^ " [-p int] [-i int] "

let speclist = [
    ("-p", Arg.Int   (fun d -> num_points := d), ": num points int parameter");
    ("-i", Arg.Int   (fun d -> num_iter   := d), ": num iterations int param");
    ("-e", Arg.Float (fun f -> evap_rate_ref := f), ": evaporation rate float param");
    ("-b", Arg.Float (fun f -> beta_ref := f), ": beta float param");
    ("-t", Arg.Float (fun f -> exp_threshold_ref := f), ": exploration threshold float param");
  ]

(* parse commandline args *)
let () = 
  Arg.parse
    speclist
    (fun x -> raise (Arg.Bad ("Bad argument: " ^ x) ))
    usage ;;

(*                  *)
type point = { x:float; y:float};;
type point_pair =  point * point ;;
type len_phermone = { len: float; mutable pher: float};;
exception Empty_list ;;

let init_pher = 0.0000001 ;; 
                            
                          
let beta = !beta_ref ;;

let cart_prod xs ys =
   List.map ( fun x -> ( List.map (fun y -> (x,y)) ys ) ) xs ;;


let pp_has_p pp p = ((fst pp) = p ) || ((snd pp) = p) ;;

let print_len_pher lp = Printf.printf "{ len: %f, pher: %f }" lp.len lp.pher
;;

let to_point (x1,y1) =  { x=x1; y=y1 }  ;;

let point_to_string p = "(" ^ string_of_float p.x ^ "," ^ string_of_float p.y ^
")" ;;
let print_point p = print_endline (point_to_string p );;
let pp_to_string pp = "(" ^ point_to_string (fst pp) ^","^ point_to_string( snd
pp) ^ ")\n" ;; 
let print_point_pair pp = print_string ( pp_to_string pp ) ;;

let reverse_pp pp = ( snd pp) , ( fst pp) ;;

let distance p1 p2 = 
  let distx = (p1.x -. p2.x) in
  let disty = (p1.y -. p2.y) in
  sqrt( distx ** 2.0 +. disty ** 2.0 ) ;; 

let ( --> ) p1 p2 = distance p1 p2 ;;

(* point pair distance  - distance between the two points in the pair *)
let pp_dist pp = 
  let pt1 = fst pp in
  let pt2 = snd pp in
  pt1 --> pt2 ;;


(***********************************************************************)
module PherMatrix = struct
  let evap_rate = !evap_rate_ref ;;

  let rec calc_distance lst = match lst with
    [] | _ :: [] -> 0.0
  | x1 :: x2 :: xs -> ( (x1 --> x2) +. calc_distance (x2 :: xs) )

  let rec calc_distance' pp_lst = match pp_lst with
    []  -> 0.0
  | x :: [] -> pp_dist x
  | x :: xs -> (pp_dist x ) +. calc_distance' xs ;;
   
  let find pm pp = try  
                    (Hashtbl.find pm pp) 
                   with Not_found ->
                    (Hashtbl.find pm ( reverse_pp pp) ) ;;

  let mem pm pp = ( Hashtbl.mem pm pp ) || ( Hashtbl.mem pm ( reverse_pp pp) ) ;;

  (* add point pair to PherMatrix hash - add both directions *)
  let add_point_pair pm p1 p2 =
     if( p1 <> p2) then begin
       let length = (p1 --> p2) in
       Hashtbl.add pm (p1,p2) {len=length; pher=init_pher};
     end

  (* following add_point_pair' is from pop_based.  It should allow
     for cutting the PherMatrix in half, but results are poor *)
  let add_point_pair' pm p1 p2 = 
     if( p1 <> p2) then begin
       let length = (p1 --> p2) in 
       let included = mem pm (p1,p2) in
       if ( not  included ) then begin (*NOTE you really want has_key here*)
         Hashtbl.add pm (p1,p2) {len=length; pher=init_pher};
       end
       else
         ();
     end

  let get_record pm pp = try  
                          (Hashtbl.find pm pp) 
                         with Not_found ->
                          (Hashtbl.find pm ( reverse_pp pp) ) ;;

  (* given a point pair find tao for the edge between *)
  let tao pm pp =
    let record = ( find pm pp ) in
      record.pher ;;
  

  (* more efficient than calling tao *)
  let quality_factor pm pp =
    let record = find pm pp in
    ( record.pher *. ((1.0 /. record.len)**beta)) ;;

     
  let make pt_list =
    let list_len = List.length pt_list in
    let pm = Hashtbl.create (  list_len * list_len )  in
    let c_prod xs ys = (*cartesian product of xs & ys *)
       List.map ( fun x -> ( List.map (fun y -> (
          add_point_pair pm x y; ); ()
       ) ys ) ) xs in
       let _ = c_prod pt_list pt_list in
    pm  ;;


  let iter pher f = Hashtbl.iter f pher

  (* update phermomone levels *)
  let update pher tour tour_len  =
    let one_minus_evap_rate = 1.0 -. evap_rate in
    Hashtbl.iter (fun k v -> 
                    let delta_tao = if (List.mem k tour) then
                                      (1.0/. tour_len) 
                                    else
                                       0.0        in 
                     if v.pher <= evap_rate then 
                     (
                        v.pher <- (init_pher +. delta_tao) 
                     )
                     else 
                        v.pher <- (((one_minus_evap_rate) *. v.pher ) +. delta_tao) ) pher ;;


  let reinforce_best pm best_tour best_tour_len = 
    let delta_tao = (1.0 /. best_tour_len) in
    List.iter  ( fun pp -> 
                      let v = get_record pm pp in
                      v.pher <- delta_tao  
               ) best_tour ;;


  let print pm = Hashtbl.iter  ( fun k v ->  print_point_pair  k ; Printf.printf " -> "; print_len_pher v; Printf.printf "\n" ) pm ;;

end;; (* module PherMatrix *)
(***********************************************************************)




let rec makeRandomPointList n = match n with 
    0 -> [] 
  | x -> {x=Random.float 300.0; y=Random.float 300.0} :: makeRandomPointList ( n-1) ;;

let without_item i lst = List.filter ( fun x -> x!=i ) lst ;;

let without_nth n lst = List.filter ( fun x -> x!=(List.nth lst n)) lst ;;

(* given a point and a list of points find the smallest distance
 * and the largest distance between the given point and points in list*)
 let rec find_distance_range p lst = 
   let rec get_dist_list list = match list with
     [] -> []
   | x::xs -> ( p --> x) :: get_dist_list xs in
       let sorted_list = List.fast_sort compare ( get_dist_list lst) in
   (List.hd sorted_list, List.nth sorted_list ( List.length sorted_list - 1) ) 
;;

let rec find_closest_point p lst =
  let rec get_closest lst' = match lst' with
     [] -> []
    |x::xs -> ( p --> x, x) :: get_closest xs in 
    let lst_wo_pt = List.filter ( fun x -> x <> p ) lst in
    let sorted_list = List.sort ( fun p1 p2 -> compare (fst p1) (fst p2) )
      (get_closest lst_wo_pt) in
    snd(List.hd sorted_list) ;; (*TODO: returns a point instead of a point pair*)

let rec find_closest_point' p lst =
  let rec get_closest lst' = match lst' with
     [] -> []
    |x::xs -> ( p --> x, x) :: get_closest xs in 
      let sorted_list = List.sort ( fun p1 p2 -> compare (fst p1) (fst p2) )
      (get_closest lst) in
      let selected_point = List.hd sorted_list in
      selected_point , (List.filter (fun i -> not( i == selected_point) ));; 


module Tour = struct

  let exploration_threshold = !exp_threshold_ref 

  let rec find_next_pt cpt pt_list pher_matrix = find_closest_point cpt pt_list

  let rec calc_distance lst = match lst with
    [] | _ :: [] -> 0.0
  | x1 :: x2 :: xs -> ( (x1 --> x2) +. calc_distance (x2 :: xs) )
   ;;


  let rec calc_distance' pp_lst = match pp_lst with
    []  -> 0.0
  | x :: [] -> pp_dist x
  | x :: xs -> (pp_dist x ) +. calc_distance' xs ;;

  let length t = calc_distance' t ;;

  let compare pp_lst1 pp_lst2 = compare ( length pp_lst1 )  ( length pp_lst2) ;;

 let prop_sel lst =
    let total = List.fold_left (fun accum p -> (snd p) +. accum) 0.0 lst in
    let randtot = Random.float total in
    let rec sel_loop v mlst = match mlst with
      [] -> raise Empty_list (*fst (List.nth lst 0) *)
    | x :: xs -> if ( (v -. snd x) <= 0.0 ) then x
                 else sel_loop (v -. snd x) xs   in
    sel_loop randtot lst ;;



  let choose_by_exploration pt dest_list pm = 
    let denom = List.fold_left ( fun accum pt' ->  accum +. PherMatrix.quality_factor pm (pt, pt')) 0.0 dest_list in
    let prob_list = List.map ( fun pt' -> (pt,pt'), (PherMatrix.quality_factor pm (pt,pt')/. denom )) dest_list in 
    fst (prop_sel prob_list) ;;

  
  let choose_by_exploitation pt pt_list pm =  (*pm not used in this case*)
    let pt' = find_closest_point pt pt_list in
    (pt,pt');;
  

  (* ACO  to construct tour *)
  let rec make_ant_tour  pt_list pm  =
    let start_point = List.nth pt_list (Random.int (List.length pt_list)) in (* get random point in list *)
    let remaining   = without_item start_point pt_list in
    let rec aco_tour  pt pts = 
      match pts with
        [] -> []
      | xs ->  let spin = Random.float 1.0 in
        let choice_func = if spin > exploration_threshold then
                 choose_by_exploration
               else
                 choose_by_exploitation  in
               let next_point_pair = choice_func pt pts pm in
               let remaining_points = without_item (snd(next_point_pair)) pts in
        next_point_pair :: ( aco_tour ( snd next_point_pair) remaining_points) in
     let tour = aco_tour start_point remaining in
     (* Close the tour *)
     let last_pair = ( List.nth tour ((List.length tour)-1)) in
     let first_pair = ( List.hd tour ) in
     ( ( snd last_pair, fst first_pair ) :: tour ) ;; 


  let rec print_tour pp_list = match pp_list with 
    []        -> Printf.printf "\n"
  | pp :: pps -> print_point_pair pp;  print_tour pps;;

end;;

let  run_aco point_list iterations point_list pm =

  let rec iter n  best best_len = match n with 
    0 ->  best
  | _ ->  
          let current_tour = Tour.make_ant_tour point_list pm in
          let current_tour_len = Tour.calc_distance' current_tour in
          let _ = PherMatrix.update pm current_tour current_tour_len  in 
          let _ =  Printf.printf "Length of tour in iteration %d is: %f\n" (iterations - n) current_tour_len in
          if current_tour_len < best_len then begin
            PherMatrix.reinforce_best pm current_tour current_tour_len ;
            iter (n-1) current_tour current_tour_len
          end
          else begin
            PherMatrix.reinforce_best pm best best_len ;
            iter (n-1) best best_len  
          end in
  let initial_tour = (Tour.make_ant_tour point_list pm) in
  iter iterations initial_tour (Tour.calc_distance' initial_tour );;
          
          
let _ =   
  Random.self_init  in 
  let point_list = makeRandomPointList !num_points in
  let pm = PherMatrix.make point_list in
  let best_tour = run_aco point_list !num_iter point_list pm in
  let best_tour_len = (Tour.calc_distance' best_tour) in
  let best_as_array = Array.of_list (List.map (fun x -> 
      let p1 = fst x in
      let p2 = snd x in
      let x1 = int_of_float ( p1.x ) in
      let y1 = int_of_float ( p1.y ) in
      let x2 = int_of_float ( p2.x ) in
      let y2 = int_of_float ( p2.y ) in
      (x1,y1,x2,y2)
  ) best_tour) in
  let matrix_as_list =  (Hashtbl.fold ( fun k v lst -> 
      let p1 = fst k in
      let p2 = snd k in
      let x1 = int_of_float ( p1.x ) in
      let y1 = int_of_float ( p1.y ) in
      let x2 = int_of_float ( p2.x ) in
      let y2 = int_of_float ( p2.y ) in
      if v.pher > 0.0 then
      (
        Printf.printf "v.pher is: %f\n" v.pher;
        (v.pher,(x1,y1,x2,y2)) :: lst
      )
      else 
        lst
  ) pm []) in
  let max_pher = Hashtbl.fold ( fun _ v accum -> 
                                  if v.pher > accum then v.pher else accum
                              ) pm 0.0 in
  (
     Tour.print_tour best_tour ;
     Printf.printf "Ant Tour distance is: %f\n" best_tour_len ;
     flush stdout;
     Graphics.open_graph "";
     Graphics.set_line_width 10;
     let _ = List.map ( fun x -> 
                   let p   = fst x in
                   let line = snd x in
                   (*let r    = int_of_float (255.0 /. ((p /. 10.0) +. 1.0) ) in *)
                   let r    =  255 - int_of_float (255.0 *. ( p /. max_pher ) ) in 

                   Graphics.set_color ( Graphics.rgb 255 r r); 
                   (* make sure that highest pheromone edges are drawn
                      last so they're not "erased" *)
                   Graphics.draw_segments [|line|] )  (List.sort (fun a b -> compare (fst a) (fst b) ) matrix_as_list) in


     (*Graphics.draw_segments matrix_as_array ;*)
     Graphics.set_line_width 3;
     Graphics.set_color Graphics.black;
     Graphics.draw_segments best_as_array ;
     Graphics.read_key ()

  );;
  

