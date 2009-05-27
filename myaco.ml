type point = { x:float; y:float};;
type point_pair =  point * point ;;
type len_phermone = { len: float; mutable pher: float } ;;
exception Empty_list ;;

let pher = 0.1 ;;
let beta = 2.0 ;;

let pp_has_p pp p = ((fst pp) = p ) || ((snd pp) = p) ;;

let print_len_pher lp = Printf.printf "{ len: %f, pher: %f }" lp.len lp.pher
;;

let to_point (x1,y1) =  { x=x1; y=y1 }  ;;

(*let print_point p = Printf.printf "( %f, %f )"  p.x  p.y ;; *)
let point_to_string p = "(" ^ string_of_float p.x ^ "," ^ string_of_float p.y ^
")" ;;
let print_point p = print_endline (point_to_string p );;
let pp_to_string pp = "(" ^ point_to_string (fst pp) ^","^ point_to_string( snd
pp) ^ ")" ;; 
let print_point_pair pp = print_string ( pp_to_string pp ) ;;

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
  let evap_rate = 0.1

  let rec calc_distance lst = match lst with
    [] | _ :: [] -> 0.0
  | x1 :: x2 :: xs -> ( (x1 --> x2) +. calc_distance (x2 :: xs) )
   
  let add_point_pair pm p1 p2 = Hashtbl.add pm (p1,p2) 
    {len=(p1-->p2); pher=pher}


  (* given a point pair find tao for the edge between *)
  let tao pm pp =
    let record = ( Hashtbl.find pm pp ) in
      record.pher ;;

  let get_record pm pp = (Hashtbl.find pm pp) ;;

  (* more efficient than calling tao *)
  let quality_factor pm pp =
    let record = get_record pm pp in
    ( record.pher *. ((1.0 /. record.len)**beta)) ;;


  let make pt_list =
    let list_len = List.length pt_list in
    let pm = Hashtbl.create (  list_len * list_len )  in
    let rec add_point_pairs lst = match lst with
      [] | _::[] -> add_point_pair pm (List.hd pt_list) ( List.nth pt_list
      ((List.length pt_list) - 1) )
    | p1 :: p2 :: ps -> ( add_point_pair pm p1 p2 ; add_point_pairs ps ) in
    add_point_pairs pt_list; 
    pm  ;;
     

    (*do we need an add?*)
 (* let add pher pp lp = Hashtbl.add pher pp lp *)
  

  let iter pher f = Hashtbl.iter f pher

  let update pher tour tour_len =
    Hashtbl.iter (fun k v -> if v.pher <= evap_rate then v.pher <- 0. 
                             else v.pher <- (v.pher -.evap_rate) ) pher 

end;; (* module PherMatrix *)
(***********************************************************************)




let rec makeRandomPointList n = match n with 
    0 -> [] 
  | x -> {x=Random.float 20.0; y=Random.float 20.0} :: makeRandomPointList ( n-1) ;;

let without_item i lst = List.filter ( fun x -> x!=i ) lst ;;

let without_nth n lst = List.filter ( fun x -> x!=(List.nth lst n)) lst ;;

(* without_item 2 [1;2;3;4;5] ;; *)

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
      let sorted_list = List.sort ( fun p1 p2 -> compare (fst p1) (fst p2) )
        (get_closest lst) in
    snd(List.hd sorted_list) ;; 

let rec find_closest_point' p lst =
  let rec get_closest lst' = match lst' with
     [] -> []
    |x::xs -> ( p --> x, x) :: get_closest xs in 
      let sorted_list = List.sort ( fun p1 p2 -> compare (fst p1) (fst p2) )
      (get_closest lst) in
      let selected_point = List.hd sorted_list in
      selected_point , (List.filter (fun i -> not( i == selected_point) ));; 


module Tour = struct

  let exploration_threshold = 0.2 (*explore 20% of the time*)

  let rec find_next_pt cpt pt_list pher_matrix = find_closest_point cpt pt_list

  let rec calc_distance lst = match lst with
    [] | _ :: [] -> 0.0
  | x1 :: x2 :: xs -> ( (x1 --> x2) +. calc_distance (x2 :: xs) )
   ;;

 let prop_sel lst =
    let total = List.fold_left (fun accum p -> (snd p) +. accum) 0.0 lst in
    let randtot = Random.float total in
    let rec sel_loop v mlst = match mlst with
      [] -> raise Empty_list (*fst (List.nth lst 0) *)
    | x :: xs -> if ( (v -. snd x) < 0.0 ) then x
                 else sel_loop (v -. snd x) xs   in
    Printf.printf "randtot is: %f\n" randtot ;
    sel_loop randtot lst ;;


  let choose_by_exploration pt pt_list pm =
    (*was:*)
    (*List.nth pt_list  (Random.int (List.length pt_list));;*)
    (*first build a list of point pairs*)
    (*not the most efficient...*)
    let pp_list = Hashtbl.fold ( fun pp' pher accum -> pp' :: accum ) pm [] in
    (* doesn't work to manufacture a point pair and look for it in
       the hashtable *)
    let denom   = List.fold_left (fun accum pp' -> accum +. PherMatrix.quality_factor pm pp') 0.0 pp_list in

    (*snd pp' below because fst in each tuple of pp_list is starting pt*)
    let prob_list = List.map ( fun pp' -> ((snd pp'), ( (PherMatrix.quality_factor pm pp')/. denom))) pp_list in
    fst (prop_sel prob_list) ;;    (* TODO: update pheromone here *)

  
  let choose_by_exploitation pt pt_list pm =  (*pm not used in this case*)
    find_closest_point pt pt_list;;
 (*
  let choose_point current_pt pt_list = 
 *)

  
  (* simple greedy algorithm to construct tour *)
  let rec make_greedy_tour'  pt_list  = 
    let start_point = List.hd pt_list in
    let remaining   = List.tl pt_list in
    let rec naive_tour  pt pts = 
    (*for now this is just a greedy tour; no pheromone consideration *)
    (* get first point *)
    match pts with 
      [] -> []
    | xs ->  let next_point = find_closest_point pt pts in
             let remaining_points = without_item next_point pts in
      next_point :: ( naive_tour ( next_point) remaining_points) in
    ( start_point :: ( naive_tour start_point remaining) )

(*
  let rec make_greedy_tour  pt_list  = 
    let start_point = List.hd pt_list in
    let remaining   = List.tl pt_list in
    let rec naive_tour  pt pts = 
    (*for now this is just a greedy tour; no pheromone consideration *)
    (* get first point *)
    match pts with 
      [] -> []
    | xs ->  let next_point = choose_by_exploitation pt pts in
             let remaining_points = without_item next_point pts in
      next_point :: ( naive_tour ( next_point) remaining_points) in
    ( start_point :: ( naive_tour start_point remaining) )
 *)

  (* ACO  to construct tour *)
  let rec make_ant_tour  pt_list pm  =
    let start_point = List.nth pt_list (Random.int (List.length pt_list)) in (* get random point in list *)
    let remaining   = without_item start_point pt_list in
    let rec aco_tour  pt pts = 
    match pts with 
      [] -> []
    | xs ->  let spin = Random.float 1.0 in 
      let choice_func = if spin < exploration_threshold then
               choose_by_exploration
             else
               choose_by_exploitation  in
             let next_point = choice_func pt pts pm in
             let remaining_points = without_item next_point pts in
      next_point :: ( aco_tour ( next_point) remaining_points) in
    ( start_point :: ( aco_tour start_point remaining) )


end;;
      

let _ = 
  Random.self_init  in 
  let pt1 = {x=0.0;y=1.0} in
  let point_list = makeRandomPointList 20 in
  let range = find_distance_range pt1 point_list in
  let next_point =  (find_closest_point pt1 point_list) in
  let pp = (List.nth  point_list 0, List.nth  point_list 1 ) in
  (*let len_pher = { len=( pp_dist pp); pher=1.0 } in*)
  let pm = PherMatrix.make point_list in 
  (*let greedy_tour = Tour.make_greedy_tour point_list in
  let greedy_tour_len = Tour.calc_distance greedy_tour in *)
  let ant_tour = (Tour.make_ant_tour point_list pm ) in
  let ant_tour_len = (Tour.calc_distance ant_tour) in
  let quality_factor_for_pp = PherMatrix.quality_factor pm pp in
  (
  (*PherMatrix.add pm pp len_pher ;*)
 
  
  Printf.printf "quality factor for first edge is: %f\n" quality_factor_for_pp;
  Printf.printf "shortest distance: %f, longest: %f\n\n" (fst range) (snd
  range);
  Printf.printf "closest point is at: %f , %f\n" (next_point.x) (next_point.y) ;
  PherMatrix.iter pm ( fun k v ->  print_point_pair  k ; Printf.printf " -> ";
  print_len_pher v; Printf.printf "\n" );

  PherMatrix.update pm ant_tour ant_tour_len ;
  PherMatrix.iter pm ( fun k v ->  print_point_pair  k ; Printf.printf " -> ";
  print_len_pher v; Printf.printf "\n" );

  (*List.iter ( fun p -> print_point p ) greedy_tour;
  Printf.printf "Greedy Tour distance is: %f\n" greedy_tour_len ;*)
  Printf.printf "Ant Tour distance is: %f\n" ant_tour_len 
  
 )
