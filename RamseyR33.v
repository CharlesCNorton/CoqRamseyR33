Require Import Bool.
Require Import Arith.
Require Import List.
Require Import Lia.
Import ListNotations.

(* Basic definitions for graphs and colorings *)

(* A vertex is just a natural number *)
Definition vertex := nat.

(* An edge is a pair of vertices *)
Definition edge := (vertex * vertex)%type.

(* A graph is represented by a list of vertices and a list of edges *)
Record graph := {
  vertices : list vertex;
  edges : list edge
}.

(* Complete graph on n vertices *)
Fixpoint complete_edges (n : nat) : list edge :=
  match n with
  | 0 => []
  | S m => 
    let prev_edges := complete_edges m in
    let new_edges := map (fun v => (m, v)) (seq 0 m) in
    prev_edges ++ new_edges
  end.

Definition complete_graph (n : nat) : graph := {|
  vertices := seq 0 n;
  edges := complete_edges n
|}.

(* Color type - Red or Blue *)
Inductive color := Red | Blue.

(* A coloring is a function from edges to colors *)
Definition coloring := edge -> color.

(* Check if an edge is in the edge list *)
Fixpoint edge_in (e : edge) (edges : list edge) : bool :=
  match edges with
  | [] => false
  | e' :: rest => 
    let (a, b) := e in
    let (a', b') := e' in
    (Nat.eqb a a' && Nat.eqb b b') || (Nat.eqb a b' && Nat.eqb b a') || edge_in e rest
  end.

(* Triangle definition - three vertices forming a triangle *)
Definition triangle := (vertex * vertex * vertex)%type.

(* Check if three vertices form a triangle in a graph *)
Definition is_triangle (g : graph) (t : triangle) : bool :=
  let '(v1, v2, v3) := t in
  edge_in (v1, v2) (edges g) && 
  edge_in (v2, v3) (edges g) && 
  edge_in (v1, v3) (edges g).

(* Check if a triangle is monochromatic under a coloring *)
Definition is_monochromatic (c : coloring) (t : triangle) : bool :=
  let '(v1, v2, v3) := t in
  let c12 := c (v1, v2) in
  let c23 := c (v2, v3) in
  let c13 := c (v1, v3) in
  match c12, c23, c13 with
  | Red, Red, Red => true
  | Blue, Blue, Blue => true
  | _, _, _ => false
  end.

(* Generate all possible triangles from a list of vertices *)
Fixpoint triangles_from_three (v1 : vertex) (v2 : vertex) (vs : list vertex) : list triangle :=
  match vs with
  | [] => []
  | v3 :: rest => (v1, v2, v3) :: triangles_from_three v1 v2 rest
  end.

Fixpoint triangles_from_two (v1 : vertex) (vs : list vertex) : list triangle :=
  match vs with
  | [] => []
  | [_] => []
  | v2 :: rest =>
    let triangles_with_v1_v2 := triangles_from_three v1 v2 rest in
    triangles_with_v1_v2 ++ triangles_from_two v1 rest
  end.

Fixpoint all_triangles (vs : list vertex) : list triangle :=
  match vs with
  | [] => []
  | [_] => []
  | [_; _] => []
  | v1 :: rest =>
    let triangles_with_v1 := triangles_from_two v1 rest in
    triangles_with_v1 ++ all_triangles rest
  end.

(* Check if any triangle in a graph is monochromatic *)
Definition has_monochromatic_triangle (g : graph) (c : coloring) : bool :=
  let triangles := all_triangles (vertices g) in
  existsb (fun t => is_triangle g t && is_monochromatic c t) triangles.

(* Specific coloring that avoids monochromatic triangles in K4 *)
Definition k4_good_coloring : coloring :=
  fun e => 
    let '(v1, v2) := e in
    match v1, v2 with
    | 0, 1 => Red  | 1, 0 => Red
    | 0, 2 => Red  | 2, 0 => Red
    | 0, 3 => Blue | 3, 0 => Blue
    | 1, 2 => Blue | 2, 1 => Blue
    | 1, 3 => Blue | 3, 1 => Blue
    | 2, 3 => Red  | 3, 2 => Red
    | _, _ => Red  (* default case *)
    end.

(* Specific coloring that avoids monochromatic triangles in K5 *)
Definition k5_good_coloring : coloring :=
  fun e => 
    let '(v1, v2) := e in
    match v1, v2 with
    | 0, 1 => Red  | 1, 0 => Red
    | 0, 2 => Red  | 2, 0 => Red
    | 0, 3 => Blue | 3, 0 => Blue
    | 0, 4 => Blue | 4, 0 => Blue
    | 1, 2 => Blue | 2, 1 => Blue
    | 1, 3 => Red  | 3, 1 => Red
    | 1, 4 => Blue | 4, 1 => Blue
    | 2, 3 => Blue | 3, 2 => Blue
    | 2, 4 => Red  | 4, 2 => Red
    | 3, 4 => Red  | 4, 3 => Red
    | _, _ => Red  (* default case *)
    end.

(* Key lemmas and theorems *)

Lemma k4_has_no_monochromatic_triangle :
  has_monochromatic_triangle (complete_graph 4) k4_good_coloring = false.
Proof.
  unfold has_monochromatic_triangle.
  unfold complete_graph.
  simpl.
  unfold all_triangles.
  simpl.
  unfold triangles_from_two.
  simpl.
  unfold triangles_from_three.
  simpl.
  (* Now we have all triangles in K4: (0,1,2), (0,1,3), (0,2,3), (1,2,3) *)
  unfold existsb.
  simpl.
  unfold is_triangle, is_monochromatic.
  simpl.
  unfold edge_in.
  simpl.
  unfold k4_good_coloring.
  simpl.
  (* Use vm_compute to verify *)
  vm_compute.
  reflexivity.
Qed.

Lemma k5_has_no_monochromatic_triangle :
  has_monochromatic_triangle (complete_graph 5) k5_good_coloring = false.
Proof.
  unfold has_monochromatic_triangle.
  unfold complete_graph.
  simpl.
  (* We need to check all triangles in K5 *)
  (* K5 has vertices [0;1;2;3;4] *)
  (* Let's compute this step by step *)
  unfold all_triangles.
  simpl.
  unfold triangles_from_two.
  simpl.
  unfold triangles_from_three.
  simpl.
  (* Now we have the explicit list of all triangles *)
  (* We need to check each one is not monochromatic *)
  unfold existsb.
  simpl.
  (* Check each triangle individually *)
  unfold is_triangle, is_monochromatic.
  simpl.
  unfold edge_in.
  simpl.
  unfold k5_good_coloring.
  simpl.
  (* This will expand to a large boolean expression *)
  (* Let's use computational reflection *)
  vm_compute.
  reflexivity.
Qed.

(* The main theorem: R(3,3) = 6 *)
(* Part 1: K5 can be 2-colored without monochromatic triangles *)
Theorem k5_avoids_monochromatic_triangle :
  exists (c : coloring), 
    has_monochromatic_triangle (complete_graph 5) c = false.
Proof.
  exists k5_good_coloring.
  exact k5_has_no_monochromatic_triangle.
Qed.

(* Part 2: Every 2-coloring of K6 has a monochromatic triangle *)
(* This is the harder part - we prove it computationally *)

(* Convert a natural number to a coloring by treating it as a binary representation *)
(* Edge ordering: (0,1)=bit0, (0,2)=bit1, ..., (0,5)=bit4, (1,2)=bit5, ..., (4,5)=bit14 *)
Definition edge_index (v1 v2 : nat) : nat :=
  if Nat.ltb v1 v2 then
    (* Standard formula for edge index in complete graph *)
    (v1 * (11 - v1)) / 2 + (v2 - v1 - 1)
  else
    (v2 * (11 - v2)) / 2 + (v1 - v2 - 1).

Definition nat_to_coloring (n : nat) : coloring :=
  fun e =>
    let '(v1, v2) := e in
    if Nat.testbit n (edge_index v1 v2) then Blue else Red.

(* Check if a specific coloring (represented as nat) has a monochromatic triangle *)
Definition coloring_has_mono_triangle (n : nat) : bool :=
  has_monochromatic_triangle (complete_graph 6) (nat_to_coloring n).

(* Convert a color to a bit *)
Definition color_to_bit (col : color) : nat :=
  match col with
  | Red => 0
  | Blue => 1
  end.

(* The 15 edges of K6 in canonical order *)
Definition k6_edges : list (nat * nat) :=
  [(0,1); (0,2); (0,3); (0,4); (0,5);
   (1,2); (1,3); (1,4); (1,5);
   (2,3); (2,4); (2,5);
   (3,4); (3,5);
   (4,5)].

(* Convert a coloring to a natural number by encoding each edge color as a bit *)
Fixpoint coloring_to_nat_aux (c : coloring) (edges : list (nat * nat)) (pos : nat) : nat :=
  match edges with
  | [] => 0
  | (v1, v2) :: rest =>
    let bit := color_to_bit (c (v1, v2)) in
    bit * Nat.pow 2 pos + coloring_to_nat_aux c rest (S pos)
  end.

Definition coloring_to_nat (c : coloring) : nat :=
  coloring_to_nat_aux c k6_edges 0.

(* Check a range of colorings *)
Fixpoint check_coloring_range (start : nat) (count : nat) : bool :=
  match count with
  | 0 => true  (* All checked in this range *)
  | S rest => 
    if coloring_has_mono_triangle start then
      check_coloring_range (S start) rest
    else
      false  (* Found a coloring without monochromatic triangle *)
  end.

(* Helper lemmas for breaking up the computation *)
(* K6 has 15 edges, so we have 2^15 = 32768 colorings to check *)
(* We'll check them in chunks of 4096 colorings each *)

Lemma check_range_0_4096 :
  check_coloring_range 0 4096 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma check_range_4096_8192 :
  check_coloring_range 4096 4096 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma check_range_8192_12288 :
  check_coloring_range 8192 4096 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma check_range_12288_16384 :
  check_coloring_range 12288 4096 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma check_range_16384_20480 :
  check_coloring_range 16384 4096 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma check_range_20480_24576 :
  check_coloring_range 20480 4096 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma check_range_24576_28672 :
  check_coloring_range 24576 4096 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.

Lemma check_range_28672_32768 :
  check_coloring_range 28672 4096 = true.
Proof.
  vm_compute.
  reflexivity.
Qed.
  
(* Combine all range checks *)
Lemma all_colorings_have_mono_triangle :
  check_coloring_range 0 32768 = true.
Proof.
  (* We prove this by breaking it into 8 chunks *)
  (* This is mathematically equivalent but computationally more manageable *)
  assert (H1: check_coloring_range 0 4096 = true) by apply check_range_0_4096.
  assert (H2: check_coloring_range 4096 4096 = true) by apply check_range_4096_8192.
  assert (H3: check_coloring_range 8192 4096 = true) by apply check_range_8192_12288.
  assert (H4: check_coloring_range 12288 4096 = true) by apply check_range_12288_16384.
  assert (H5: check_coloring_range 16384 4096 = true) by apply check_range_16384_20480.
  assert (H6: check_coloring_range 20480 4096 = true) by apply check_range_20480_24576.
  assert (H7: check_coloring_range 24576 4096 = true) by apply check_range_24576_28672.
  assert (H8: check_coloring_range 28672 4096 = true) by apply check_range_28672_32768.
  
  (* Now we need to prove that checking in chunks is equivalent to checking all at once *)
  (* This would require a lemma about check_coloring_range composition *)
  (* For now, we can verify directly *)
  vm_compute.
  reflexivity.
Qed.

(* Helper: 2^n > 0 *)
Lemma pow2_pos : forall n, 0 < Nat.pow 2 n.
Proof. induction n; simpl; lia. Qed.

(* Helper: color_to_bit returns 0 or 1 *)
Lemma color_to_bit_bound : forall col, color_to_bit col <= 1.
Proof. destruct col; simpl; lia. Qed.

(* Key lemma: coloring_to_nat produces values in valid range *)
Lemma coloring_to_nat_aux_bound : forall c edges pos,
  coloring_to_nat_aux c edges pos < Nat.pow 2 (pos + length edges).
Proof.
  intros c edges. revert c.
  induction edges as [|[v1 v2] rest IH]; intros c pos; simpl.
  - rewrite Nat.add_0_r. apply pow2_pos.
  - specialize (IH c (S pos)).
    assert (Hbit: color_to_bit (c (v1, v2)) <= 1) by apply color_to_bit_bound.
    assert (Hpow: Nat.pow 2 pos > 0) by apply pow2_pos.
    assert (Heq: S pos + length rest = S (pos + length rest)) by lia.
    rewrite Heq in IH.
    assert (Hpow2: Nat.pow 2 (S (pos + length rest)) = 2 * Nat.pow 2 (pos + length rest)).
    { simpl. lia. }
    rewrite Hpow2 in IH.
    destruct (color_to_bit (c (v1, v2))); simpl in *; lia.
Qed.

Lemma coloring_to_nat_bound : forall c,
  coloring_to_nat c < 32768.
Proof.
  intro c.
  unfold coloring_to_nat.
  assert (H := coloring_to_nat_aux_bound c k6_edges 0).
  unfold k6_edges in H. simpl in H. exact H.
Qed.

(* The critical lemma: check_coloring_range returns true means all colorings in range have mono triangle *)
Lemma check_range_implies_mono : forall start count n,
  check_coloring_range start count = true ->
  start <= n < start + count ->
  coloring_has_mono_triangle n = true.
Proof.
  intros start count.
  revert start.
  induction count; intros start n Hcheck Hrange.
  - lia.
  - simpl in Hcheck.
    destruct (coloring_has_mono_triangle start) eqn:E.
    + destruct (Nat.eq_dec n start).
      * subst. exact E.
      * apply IHcount with (start := S start); try lia.
        exact Hcheck.
    + discriminate.
Qed.

(* For any n < 32768, the corresponding coloring has a monochromatic triangle *)
Lemma all_nats_have_mono : forall n,
  n < 32768 ->
  coloring_has_mono_triangle n = true.
Proof.
  intros n Hn.
  apply check_range_implies_mono with (start := 0) (count := 32768).
  - exact all_colorings_have_mono_triangle.
  - lia.
Qed.

(* Two colorings that agree on all K6 edges give same result for has_monochromatic_triangle *)
Definition colorings_agree_on_k6 (c1 c2 : coloring) : Prop :=
  forall v1 v2, v1 < 6 -> v2 < 6 -> v1 <> v2 -> c1 (v1, v2) = c2 (v1, v2).

Lemma edge_index_correct : forall v1 v2,
  v1 < 6 -> v2 < 6 -> v1 < v2 ->
  edge_index v1 v2 < 15.
Proof.
  intros v1 v2 H1 H2 Hlt.
  unfold edge_index.
  destruct (Nat.ltb v1 v2) eqn:E.
  - destruct v1, v2; simpl; try lia.
    all: destruct v2; simpl; try lia.
    all: destruct v2; simpl; try lia.
    all: destruct v2; simpl; try lia.
    all: destruct v2; simpl; try lia.
    all: destruct v2; simpl; try lia.
  - apply Nat.ltb_ge in E. lia.
Qed.

Lemma testbit_pow2 : forall n k,
  Nat.testbit (Nat.pow 2 k) k = true.
Proof.
  intros n k.
  induction k; simpl.
  - reflexivity.
  - rewrite Nat.add_0_r.
    rewrite Nat.testbit_succ_r_div2.
    rewrite Nat.pow_succ_r; try lia.
    rewrite Nat.div_mul; try lia.
    exact IHk.
Qed.

(* Key: the triangles in K6 only look at K6 edges *)
Lemma has_mono_depends_only_on_k6_edges : forall c1 c2,
  (forall v1 v2, In (v1, v2) k6_edges -> c1 (v1, v2) = c2 (v1, v2)) ->
  (forall v1 v2, In (v2, v1) k6_edges -> c1 (v1, v2) = c2 (v1, v2)) ->
  has_monochromatic_triangle (complete_graph 6) c1 =
  has_monochromatic_triangle (complete_graph 6) c2.
Proof.
  intros c1 c2 Hfwd Hrev.
  unfold has_monochromatic_triangle, complete_graph.
  simpl.
  f_equal.
  apply map_ext.
  intros [[a b] d].
  unfold is_triangle, is_monochromatic.
  simpl.
  f_equal.
  assert (Hab: c1 (a, b) = c2 (a, b)).
  { destruct (Nat.lt_trichotomy a b) as [Hlt|[Heq|Hgt]].
    - apply Hfwd. unfold k6_edges.
      destruct a, b; simpl in *; try lia; auto.
      all: destruct b; simpl in *; try lia; auto.
      all: destruct b; simpl in *; try lia; auto.
      all: destruct b; simpl in *; try lia; auto.
      all: destruct b; simpl in *; try lia; auto.
    - subst. reflexivity.
    - apply Hrev. unfold k6_edges.
      destruct a, b; simpl in *; try lia; auto.
      all: destruct a; simpl in *; try lia; auto.
      all: destruct a; simpl in *; try lia; auto.
      all: destruct a; simpl in *; try lia; auto.
      all: destruct a; simpl in *; try lia; auto. }
  assert (Hbd: c1 (b, d) = c2 (b, d)).
  { destruct (Nat.lt_trichotomy b d) as [Hlt|[Heq|Hgt]].
    - apply Hfwd. unfold k6_edges.
      destruct b, d; simpl in *; try lia; auto.
      all: destruct d; simpl in *; try lia; auto.
      all: destruct d; simpl in *; try lia; auto.
      all: destruct d; simpl in *; try lia; auto.
      all: destruct d; simpl in *; try lia; auto.
    - subst. reflexivity.
    - apply Hrev. unfold k6_edges.
      destruct b, d; simpl in *; try lia; auto.
      all: destruct b; simpl in *; try lia; auto.
      all: destruct b; simpl in *; try lia; auto.
      all: destruct b; simpl in *; try lia; auto.
      all: destruct b; simpl in *; try lia; auto. }
  assert (Had: c1 (a, d) = c2 (a, d)).
  { destruct (Nat.lt_trichotomy a d) as [Hlt|[Heq|Hgt]].
    - apply Hfwd. unfold k6_edges.
      destruct a, d; simpl in *; try lia; auto.
      all: destruct d; simpl in *; try lia; auto.
      all: destruct d; simpl in *; try lia; auto.
      all: destruct d; simpl in *; try lia; auto.
      all: destruct d; simpl in *; try lia; auto.
    - subst. reflexivity.
    - apply Hrev. unfold k6_edges.
      destruct a, d; simpl in *; try lia; auto.
      all: destruct a; simpl in *; try lia; auto.
      all: destruct a; simpl in *; try lia; auto.
      all: destruct a; simpl in *; try lia; auto.
      all: destruct a; simpl in *; try lia; auto. }
  rewrite Hab, Hbd, Had.
  reflexivity.
Qed.

(* Computational verification that nat_to_coloring (coloring_to_nat c) agrees with c on K6 edges *)
Lemma nat_coloring_roundtrip_k6 : forall c v1 v2,
  In (v1, v2) k6_edges ->
  nat_to_coloring (coloring_to_nat c) (v1, v2) = c (v1, v2).
Proof.
  intros c v1 v2 Hin.
  unfold nat_to_coloring, coloring_to_nat.
  unfold k6_edges in *.
  simpl in Hin.
  repeat match goal with
  | H: _ \/ _ |- _ => destruct H as [H|H]
  | H: (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H: False |- _ => contradiction
  end;
  unfold edge_index, coloring_to_nat_aux, color_to_bit; simpl;
  destruct (c (0, 1)), (c (0, 2)), (c (0, 3)), (c (0, 4)), (c (0, 5)),
           (c (1, 2)), (c (1, 3)), (c (1, 4)), (c (1, 5)),
           (c (2, 3)), (c (2, 4)), (c (2, 5)),
           (c (3, 4)), (c (3, 5)),
           (c (4, 5)); reflexivity.
Qed.

Lemma nat_coloring_roundtrip_k6_rev : forall c v1 v2,
  In (v2, v1) k6_edges ->
  nat_to_coloring (coloring_to_nat c) (v1, v2) = c (v1, v2).
Proof.
  intros c v1 v2 Hin.
  unfold nat_to_coloring, coloring_to_nat.
  unfold k6_edges in *.
  simpl in Hin.
  repeat match goal with
  | H: _ \/ _ |- _ => destruct H as [H|H]
  | H: (_, _) = (_, _) |- _ => inversion H; subst; clear H
  | H: False |- _ => contradiction
  end;
  unfold edge_index, coloring_to_nat_aux, color_to_bit; simpl;
  destruct (c (0, 1)), (c (0, 2)), (c (0, 3)), (c (0, 4)), (c (0, 5)),
           (c (1, 2)), (c (1, 3)), (c (1, 4)), (c (1, 5)),
           (c (2, 3)), (c (2, 4)), (c (2, 5)),
           (c (3, 4)), (c (3, 5)),
           (c (4, 5)); reflexivity.
Qed.

(* Convert the computational result to the theorem we need *)
Theorem k6_has_monochromatic_triangle :
  forall (c : coloring),
    has_monochromatic_triangle (complete_graph 6) c = true.
Proof.
  intro c.
  assert (H := coloring_to_nat_bound c).
  assert (Hmono := all_nats_have_mono (coloring_to_nat c) H).
  unfold coloring_has_mono_triangle in Hmono.
  rewrite <- Hmono.
  apply has_mono_depends_only_on_k6_edges.
  - intros v1 v2 Hin. symmetry. apply nat_coloring_roundtrip_k6. exact Hin.
  - intros v1 v2 Hin. symmetry. apply nat_coloring_roundtrip_k6_rev. exact Hin.
Qed.

(* Main theorem: R(3,3) = 6 *)
Theorem ramsey_3_3_equals_6 :
  (exists (c : coloring), 
     has_monochromatic_triangle (complete_graph 5) c = false) /\
  (forall (c : coloring),
     has_monochromatic_triangle (complete_graph 6) c = true).
Proof.
  split.
  - exact k5_avoids_monochromatic_triangle.
  - exact k6_has_monochromatic_triangle.
Qed.

(* Corollary: 6 is the minimum number for guaranteed monochromatic triangle *)
Corollary ramsey_number_3_3 :
  forall n, n < 6 -> 
    exists (c : coloring), 
      has_monochromatic_triangle (complete_graph n) c = false.
Proof.
  intros n H.
  (* Case analysis on n < 6 *)
  destruct n as [|[|[|[|[|[|]]]]]].
  
  (* Case n = 0: K0 has no triangles *)
  - exists k5_good_coloring.
    unfold has_monochromatic_triangle, complete_graph.
    simpl.
    reflexivity.
    
  (* Case n = 1: K1 has no triangles *)  
  - exists k5_good_coloring.
    unfold has_monochromatic_triangle, complete_graph.
    simpl.
    reflexivity.
    
  (* Case n = 2: K2 has no triangles *)
  - exists k5_good_coloring.
    unfold has_monochromatic_triangle, complete_graph.
    simpl.
    reflexivity.
    
  (* Case n = 3: K3 has one triangle, can be avoided *)
  - exists k5_good_coloring.
    unfold has_monochromatic_triangle, complete_graph.
    simpl.
    unfold all_triangles, triangles_from_two, triangles_from_three.
    simpl.
    unfold existsb, is_triangle, is_monochromatic.
    simpl.
    unfold edge_in, k5_good_coloring.
    simpl.
    reflexivity.
    
  (* Case n = 4: K4 can avoid monochromatic triangles *)
  - exists k4_good_coloring.
    exact k4_has_no_monochromatic_triangle.
    
  (* Case n = 5: Use our proven result *)
  - exact k5_avoids_monochromatic_triangle.
  
  (* Case n >= 6: impossible since n < 6 *)
  - lia.
Qed.
