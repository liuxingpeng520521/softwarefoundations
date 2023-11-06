(** * Selection:  Selection Sort *)

(** If you don't recall selection sort or haven't seen it in
    a while, see Wikipedia or read any standard textbook; some
    suggestions can be found in [Sort]. *)

(** The specification for sorting algorithms we developed in
    [Sort] can also be used to verify selection sort.  The
    selection-sort program itself is interesting, because writing it
    in Coq will cause us to explore a new technique for convincing Coq
    that a function terminates. *)

(** A couple of notes on efficiency:

    - Selection sort, like insertion sort, runs in quadratic time.
      But selection sort typically makes many more comparisons than
      insertion sort, so insertion sort is usually preferable for
      sorting small inputs.  Selection sort can beat insertion sort if
      the cost of swapping elements is vastly higher than the cost of
      comparing them, but that doesn't apply to functional lists.

    - What you should really never use is bubble sort.  "Bubble sort
      would be the wrong way to go."  Everybody should know that!  See
      this video for a definitive statement:
        {https://www.youtube.com/watch?v=k4RRi_ntQc8&t=34} *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From VFA Require Import Perm.
Hint Constructors Permutation : core.
From Coq Require Export Lists.List.  (* for exercises involving [List.length] *)

(* ################################################################# *)
(** * The Selection-Sort Program  *)

(** Selection sort on lists is more challenging to code in Coq
    than insertion sort was. First, we write a helper function
    to select the smallest element. *)

(* [select x l] is [(y, l')], where [y] is the smallest element
   of [x :: l], and [l'] is all the remaining elements of [x :: l]. *)
Fixpoint select (x: nat) (l: list nat) : nat * list nat :=
  match l with
  | [] => (x, [])
  | h :: t =>
    if x <=? h
    then let (j, l') := select x t
         in (j, h :: l')
    else let (j, l') := select h t
         in (j, x :: l')
  end.

(** Selection sort should repeatedly extract the smallest element and
    make a list of the results. But the following attempted definition
    fails: *)

Fail Fixpoint selsort (l : list nat) : list nat :=
  match l with
  | [] => []
  | x :: r => let (y, r') := select x r
            in y :: selsort r'
  end.

(** Coq rejects [selsort] because it doesn't satisfy Coq's
    requirements for termination.  The problem is that the recursive
    call in [selsort] is not _structurally decreasing_: the argument
    [r'] at the call site is not known to be a smaller part of the
    original input [l]. Indeed, [select] might not return such a list.
    For example, [select 1 [0; 2]] is [(0, [1; 2])], but [[1; 2]] is
    not a part of [[0; 2]]. *)

(** There are several ways to fix this problem. One programming
    pattern is to provide _fuel_: an extra argument that has no use in
    the algorithm except to bound the amount of recursion.  The [n]
    argument, below, is the fuel. When it reaches [0], the recursion
    terminates. *)

Fixpoint selsort (l : list nat) (n : nat) : list nat :=
  match l, n with
  | _, O => []  (* ran out of fuel *)
  | [], _ => []
  | x :: r, S n' => let (y, r') := select x r
                  in y :: selsort r' n'
end.

(** If fuel runs out, we get the wrong output. *)

Example out_of_fuel: selsort [3;1;4;1;5] 3 <> [1;1;3;4;5].
Proof.
  simpl. intro. discriminate.
Qed.

(** Extra fuel isn't a problem though. *)

Example extra_fuel: selsort [3;1;4;1;5] 10 = [1;1;3;4;5].
Proof.
  simpl. reflexivity.
Qed.

(** The exact amount of fuel needed is the length of the input list.
    So that's how we define [selection_sort]: *)

Definition selection_sort (l : list nat) : list nat :=
  selsort l (length l).

Example sort_pi :
  selection_sort [3;1;4;1;5;9;2;6;5;3;5] = [1;1;2;3;3;4;5;5;5;6;9].
Proof.
  unfold selection_sort.
  simpl. reflexivity.
Qed.

(* ################################################################# *)
(** * Proof of Correctness *)

(** We begin by repeating from [Sort] the specification of a
    correct sorting algorithm: it rearranges the elements into a list
    that is totally ordered. *)

Inductive sorted: list nat -> Prop :=
 | sorted_nil: sorted []
 | sorted_1: forall i, sorted [i]
 | sorted_cons: forall i j l, i <= j -> sorted (j :: l) -> sorted (i :: j :: l).

Hint Constructors sorted : core.

Definition is_a_sorting_algorithm (f: list nat -> list nat) := forall al,
    Permutation al (f al) /\ sorted (f al).

(** In the following exercises, you will prove that selection sort
    is a correct sorting algorithm.  You might wish to keep track
    of the lemmas you have proved, so that you can spot places to
    use them later. *)

(** Depending on the path you have followed through _Software
    Foundations_ it might have been a while since you have worked with
    pairs.  Here's a brief reminder of how [destruct] can be used to
    break a pair apart into its components.  A similar technique
    will be needed in many of the following proofs. *)
Example pairs_example : forall (a c x : nat) (b d l : list nat),
    (a, b) = (let (c, d) := select x l in (c, d)) ->
    (a, b) = select x l.
Proof.
  intros. destruct (select x l) as [c' d'] eqn:E. auto.
Qed.

(** **** Exercise: 2 stars, standard (select_perm) *)

(** Prove that [select] returns a permutation of its input. Proceed by
    induction on [l].  The [inv] tactic defined at the end of
    [Perm] will be helpful. The [eauto] tactic] will be helpful
    at finding instantiations for [perm_trans]. *)
Ltac gen x := generalize dependent x.
Lemma select_perm: forall x l y r,
    select x l = (y, r) -> Permutation (x :: l) (y :: r).
Proof.
  intros x l. gen x.
  induction l; simpl; intros x y r H.
  - injection H as Hl Hr; subst.
    constructor.
    constructor.
  - bdestruct (x<=? a).
    + destruct (select x l) eqn:E.
      injection H as Hl Hr; subst.
      change (x :: a :: l) with ([x] ++ [a] ++ l).
      change (y :: a :: l0) with ([y] ++ [a] ++ l0).
      apply perm_trans with ([a] ++ [x] ++ l).
      * apply Permutation_app_swap_app.
      * apply perm_trans with ([a] ++ [y] ++ l0).
        ** simpl. 
           apply perm_skip.
           apply IHl.
           assumption.
        ** apply Permutation_app_swap_app.
    + destruct (select a l) eqn:E.
      injection H as Hl Hr; subst.
      change (y :: x :: l0) with ([y] ++ [x] ++ l0).
      apply perm_trans with ([x] ++ [y] ++ l0).
      * simpl.
        apply perm_skip.
        apply IHl.
        assumption.
      * apply Permutation_app_swap_app.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (select_rest_length) *)

(** Prove that [select] returns a list that has the correct
    length. You can do this without induction if you make use of
    [select_perm]. *)

Lemma select_rest_length : forall x l y r,
    select x l = (y, r) -> length l = length r.
Proof.
  intros.
  apply select_perm in H.
  apply Permutation_length in H.
  simpl in H.
  lia.
Qed.

(** [] *)

(** **** Exercise: 3 stars, standard (selsort_perm) *)

(** Prove that if you provide sufficient fuel, [selsort] produces a
    permutation.  Proceed by induction on [n]. *)

Lemma selsort_perm: forall n l,
    length l = n -> Permutation l (selsort l n).
Proof.
  intros n.
  induction n; intros l Hlen; simpl in Hlen.
  - simpl. destruct l. 
      constructor. 
      simpl in Hlen. discriminate.
  - unfold selsort.
    fold selsort.
    destruct l.
    + constructor.
    + destruct (select n0 l) eqn:E.
      apply select_perm in E.
      apply perm_trans with (n1 :: l0).
      * assumption.
      * apply perm_skip.
        apply IHn.
        simpl in Hlen.
        Search Permutation.
        apply Permutation_length in E.
        simpl in E.
        lia.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (selection_sort_perm) *)

(** Prove that [selection_sort] produces a permutation. *)

Lemma selection_sort_perm: forall l,
    Permutation l (selection_sort l).
Proof.
  intro l.
  unfold selection_sort.
  apply selsort_perm.
  reflexivity.
Qed.

(** **** Exercise: 2 stars, standard (select_fst_leq) *)

(** Prove that the first component of [select x _] is no bigger than
    [x]. Proceed by induction on [al]. *)

Lemma select_fst_leq: forall al bl x y,
    select x al = (y, bl) ->
    y <= x.
Proof.
  intro al.
  induction al; simpl; intros bl x y Hsel.
  - injection Hsel as Exy.
    lia.
  - bdestruct ( x <=? a).
    + destruct (select x al) eqn:E.
      injection Hsel as Hs1 Hs2.
      subst.
      apply IHal with l.
      assumption.
    + destruct (select a al) eqn:E.
      injection Hsel as Hs1 Hs2.
      subst.
      assert (G: y <= a). {
        apply IHal with l.
        assumption.
      }
      lia.
Qed.

(** To represent the concept of comparing a number to a list, we
    introduce a new notation: *)

Definition le_all x xs := Forall (fun y => x <= y) xs.
Hint Unfold le_all : core.
Infix "<=*" := le_all (at level 70, no associativity).

(** **** Exercise: 1 star, standard (le_all__le_one) *)

(** Prove that if [y] is no more than any of the elements of [lst],
    and if [n] is in [lst], then [y] is no more than [n]. Hint: a
    library theorem about [Forall] and [In] will make this easy. *)

Lemma le_all__le_one : forall lst y n,
    y <=* lst -> In n lst -> y <= n.
Proof.
  intros.
  induction H.
  -inversion H0.
  - destruct H0.
    + lia.
    + apply IHForall. apply H0.
Qed.

(** [] *)

(** **** Exercise: 2 stars, standard (select_smallest) *)

(** Prove that the first component of [select _ _] is no bigger than
    any of the elements in the second component. Proceed by induction
    on [al]. *)

Lemma select_smallest: forall al bl x y,
    select x al = (y, bl) ->
    y <=* bl.
Proof.
  intros al. induction al;simpl;intros.
  +injection H as Hl Hr;subst.
   unfold le_all. apply Forall_nil.
  +bdestruct (x <=? a).
   -destruct(select x al) eqn:E.
    injection H as Hl Hr;subst.
    remember E as F. clear HeqF.
    apply IHal in E.
    apply Forall_cons.
    *apply select_fst_leq in F. lia.
    *assumption.
   -destruct(select a al) eqn:E.
   injection H as Hl Hr;subst.
   remember E as F. clear HeqF.
   apply IHal in E.
   apply Forall_cons.
   *apply select_fst_leq in F. lia.
   *assumption.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (select_in) *)

(** Prove that the element returned by [select] must be one of the
    elements in its input. Proceed by induction on [al]. *)

Lemma select_in : forall al bl x y,
    select x al = (y, bl) ->
    In y (x :: al).
Proof.
  intros al. induction al;simpl;intros.
  +injection H as Hl Hr. left;assumption.
  +bdestruct (x <=? a).
    -destruct(select x al) eqn:E.
    injection H as Hl Hr;subst.
    apply IHal in E.
    inversion E;subst.
     *left. reflexivity.
     *repeat(right). assumption.
    -destruct(select a al) eqn:E.
    injection H as Hl Hr;subst.
    apply IHal in E.
    inversion E;subst.
     *right. left. reflexivity.
     *repeat(right). assumption.
Qed.


(** [] *)

(** **** Exercise: 3 stars, standard (cons_of_small_maintains_sort) *)

(** Prove that adding an element to the beginning of a
    selection-sorted list maintains sortedness, as long as the element
    is small enough and enough fuel is provided. No induction is
    needed. *)

Lemma cons_of_small_maintains_sort: forall bl y n,
    n = length bl ->
    y <=* bl ->
    sorted (selsort bl n) ->
    sorted (y :: selsort bl n).
Proof.
  intros bl y n. gen bl. gen y.
  induction n; simpl; intros y bl Hn Hle Hsort.
  -destruct bl;constructor.
  - destruct bl as [| bh bt ].
    +constructor.
    + destruct (select bh bt) eqn:E.
      constructor.
      * apply select_in in E.
        apply le_all__le_one with  (bh :: bt).
          assumption.
          assumption.
      * apply Hsort.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (selsort_sorted) *)

(** Prove that [selsort] produces a sorted list when given
    sufficient fuel.  Proceed by induction on [n].  This proof
    will make use of a few previous lemmas. *)

Lemma selsort_sorted : forall n al,
    length al = n -> sorted (selsort al n).
Proof.
  intro n.
  induction n; simpl in *; intros al Hlen.
  - destruct al.
    + constructor.
    + discriminate Hlen.
  - destruct al.
    + discriminate Hlen.
    + destruct (select n0 al) eqn:E.
      Print sorted.
      apply cons_of_small_maintains_sort.
      * simpl in Hlen. apply select_rest_length in E. lia.
      * apply select_smallest in E. assumption.
      * apply IHn. apply select_rest_length in E. simpl in Hlen. lia.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (selection_sort_sorted) *)

(** Prove that [selection_sort] produces a sorted list. *)

Lemma selection_sort_sorted : forall al,
    sorted (selection_sort al).
Proof.
  unfold selection_sort.
  intros al.
  apply selsort_sorted.
  reflexivity.
Qed.

(** **** Exercise: 1 star, standard (selection_sort_is_correct) *)

(** Finish the proof of correctness! *)

Theorem selection_sort_is_correct :
  is_a_sorting_algorithm selection_sort.
  Proof.
    intro a.
    split.
    - apply selection_sort_perm.
    - apply selection_sort_sorted.
  Qed.

(** [] *)

(* ################################################################# *)
(** * Recursive Functions That are Not Structurally Recursive *)

(** We used fuel above to create a structurally recursive
    version of [selsort] that Coq would accept as terminating.  The
    amount of fuel decreased at each call, until it reached zero.
    Since the fuel argument was structurally decreasing, Coq accepted
    the definition.  But it complicated the implementation of
    [selsort] and the proofs about it.

    Coq provides a command [Function] that implements a similar idea
    as fuel, but without requiring the function definition to be
    structurally recursive.  Instead, the function is annotated with a
    _measure_ that is decreasing at each recursive call. To activate
    such annotations, we need to load a library. *)

Require Import Recdef.  (* needed for [measure] feature *)

(** Now we can add a [measure] annotation on the definition of
    [selsort] to tell Coq that each recursive call decreases the
    length of [l]: *)

Function selsort' l {measure length l} :=
  match l with
  | [] => []
  | x :: r => let (y, r') := select x r
            in y :: selsort' r'
end.

(** The [measure] annotation takes two parameters, a measure
    function and an argument name.  Above, the function is [length]
    and the argument is [l].  The function must return a [nat] when
    applied to the argument.  Coq then challenges us to prove that
    [length] applied to [l] is actually decreasing at every recursive
    call. *)

Proof.
  intros l x r HL y r' Hsel.
  apply select_rest_length in Hsel. inv Hsel. simpl. lia.
Defined.

(** The proof must end with [Defined] instead of [Qed].  That
    ensures the function's body can be used in computation.  For
    example, the following unit test succeeds, but try changing
    [Defined] to [Qed] and see how it gets stuck. *)

Example selsort'_example : selsort' [3;1;4;1;5;9;2;6;5] = [1;1;2;3;4;5;5;6;9].
Proof. reflexivity. Qed.

(** The definition of [selsort'] is completed by the [Function]
    command using a helper function that it generates,
    [selsort'_terminate].  Neither of them is going to be useful to
    unfold in proofs: *)

Print selsort'.
Print selsort'_terminate.

(** Instead, anywhere you want to unfold or simplify [selsort'], you
    should now rewrite with [selsort'_equation], which was
    automatically defined by the [Function] command: *)

Check selsort'_equation.

(** **** Exercise: 1 star, standard (selsort'_perm) *)

(** Hint: Follow the same strategy as [selsort_perm]. In our solution,
    there was only a one-line change. *)

Lemma selsort'_perm : forall n l,
    length l = n -> Permutation l (selsort' l).
Proof.
  intros n.
  induction n; intros l Hlen; simpl in Hlen.
  - simpl. destruct l. 
      constructor. 
      simpl in Hlen. discriminate.
  - rewrite selsort'_equation.
    destruct l.
    + constructor.
    + destruct (select n0 l) eqn:E.
      apply select_perm in E.
      apply perm_trans with (n1 :: l0).
      * assumption.
      * apply perm_skip.
        apply IHn.
        simpl in Hlen.
        Search Permutation.
        apply Permutation_length in E.
        simpl in E.
        lia.
Qed.

(** [] *)

(** **** Exercise: 1 star, standard (cons_of_small_maintains_sort') *)

(** Hint: Follow the same strategy as
    [cons_of_small_maintains_sort']. In our solution, there was only a
    one-line change. *)

Lemma cons_of_small_maintains_sort': forall bl y,
    y <=* bl ->
    sorted (selsort' bl) ->
    sorted (y :: selsort' bl).
Proof. 
  intros. destruct (selsort' bl) eqn:E.
  + apply sorted_1.
  + apply sorted_cons. apply le_all__le_one with (n:=n) in H.
    assumption. 
    (* In n bl *) rewrite selsort'_equation in E.
    destruct bl eqn:EE. inversion E.
    destruct (select n0 l0) as [n' l'] eqn:EEE.
    apply select_in with (bl:=l'). inversion E. subst. assumption. 
    assumption.
Qed.

(** **** Exercise: 1 star, standard (selsort'_sorted) *)

(** Hint: Follow the same strategy as [selsort_sorted]. In our
    solution, there were only three small changes. *)

Lemma selsort'_sorted : forall n al,
    length al = n -> sorted (selsort' al).
Proof.
  induction n; intros.
  - apply length_zero_iff_nil in H. rewrite H. auto.
  - rewrite selsort'_equation. destruct al eqn:E.
    + auto.
    + destruct (select n0 l) as [y r'] eqn:EE.
      (* sorted (selsort' r') y<=*r' *)
      apply select_smallest in EE as H1.
      inversion H. apply select_rest_length in EE as H3.
      rewrite H3 in H2. apply IHn in H2.
      apply cons_of_small_maintains_sort'; assumption.
Qed.
(** **** Exercise: 1 star, standard (selsort'_is_correct) *)

(** Finish the proof of correctness! *)

Theorem selsort'_is_correct :
  is_a_sorting_algorithm selsort'.
Proof. 
  unfold is_a_sorting_algorithm. intros. split.
  apply selsort'_perm with (n:=length al); reflexivity.
  apply selsort'_sorted with (n:=length al); reflexivity.
Qed.

(* ################################################################# *)
(** * Selection Sort with Multisets (Optional) *)

(** This section relies on [Multiset]. *)

From VFA Require Import Multiset.

(** Let's prove the correctness of [selection_sort] using multisets
    instead of permutations. These exercises and their proofs were
    contributed by William Ma. *)

(** **** Exercise: 3 stars, standard, optional (select_contents) *)

Lemma select_contents : forall al bl x y,
  select x al = (y, bl) ->
  union (singleton x) (contents al) = union (singleton y) (contents bl).
Proof.
  induction al;intros;simpl.
  +injection H as Hl Hr;subst. reflexivity.
  +unfold select in H. fold select in H. bdestruct(x<=?a).
   -destruct(select x al) as [j l'] eqn:EE. injection H as Hl Hr;subst.
    simpl. 
    rewrite union_assoc. rewrite union_comm with (singleton x) (singleton a). rewrite<-union_assoc. 
    rewrite union_assoc with (singleton y) (singleton a) (contents l').
    rewrite union_comm with (singleton y) (singleton a).
    rewrite<-union_assoc. 
    apply IHal in EE. rewrite EE. reflexivity.
   -destruct(select a al) as [j l'] eqn:EE. injection H as Hl Hr;subst.
    simpl. 
    rewrite union_assoc with (singleton y) (singleton x) (contents l').
    rewrite union_comm with (singleton y) (singleton x).
    rewrite<-union_assoc. 
    apply IHal in EE. rewrite EE. reflexivity.
Qed.
  

(** [] *)

(** **** Exercise: 3 stars, standard, optional (selection_sort_contents) *)

Lemma selection_sort_contents : forall n l,
  length l = n ->
  contents l = contents (selection_sort l).
Proof. 
  induction n;intros;simpl.
  +rewrite length_zero_iff_nil in H. rewrite H. reflexivity.
  +induction l;simpl.
   -reflexivity.
   -inversion H.
   unfold selection_sort. simpl. destruct (select a l) as [y r'] eqn:EE. simpl.
   remember EE as FF. clear HeqFF. apply select_rest_length in EE. rewrite EE.
   assert (selection_sort r'=selsort r' (length r')) . { reflexivity. }
   rewrite<-H0. assert(length r'=n). {rewrite<-H1. symmetry in EE. apply EE.  }
   apply IHn in H2. rewrite<-H2. apply select_contents. apply FF.
Qed.


(** [] *)

(** **** Exercise: 2 stars, standard, optional (sorted_iff_sorted) *)

Lemma sorted_iff_sorted : forall l, sorted l <-> Sort.sorted l.
Proof. 
  split.
  - intros. induction H.
    + constructor.
    + constructor.
    + constructor; try (assumption).
  - intros. induction H; try (constructor).
    + assumption. + try (assumption).
Qed.
(** **** Exercise: 1 star, standard, optional (selection_sort_correct') *)

Theorem selection_sort_correct' :
  is_a_sorting_algorithm' selection_sort.
Proof. 
  unfold is_a_sorting_algorithm'. intros.
  split.
  - apply selection_sort_contents with (n:=(length al)). reflexivity.
  - apply sorted_iff_sorted. apply selection_sort_sorted.
Qed.

(** [] *)

(* 2023-08-23 11:34 *)
