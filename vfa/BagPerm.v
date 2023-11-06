(** * BagPerm:  Insertion Sort With Bags *)

(** We have seen how to specify algorithms on "collections", such as
    sorting algorithms, using [Permutation]s.  Instead of using
    permutations, another way to specify these algorithms is to use
    _bags_ (also called _multisets_), which we introduced in [Lists].
    A _set_ of values is like a list with no repeats where
    the order does not matter.  A _multiset_ is like a list, possibly
    with repeats, where the order does not matter.  Whereas the principal
    query on a set is whether a given element appears in it, the
    principal query on a bag is _how many_ times a given element appears 
    in it. *)

From Coq Require Import Strings.String. (* for manual grading *)
From Coq Require Import Setoid Morphisms.
From VFA Require Import Perm.
From VFA Require Import Sort.

(** To keep this chapter more self-contained, 
we restate the critical definitions from [Lists].  *)
Definition bag := list nat.

Fixpoint count (v:nat) (s:bag) : nat :=
  match s with
  | nil => 0
  | h :: t =>
      (if h =? v then 1 else 0) + count v t
  end.

(** We will say two bags are _equivalent_ if they have the same number
    of copies of every possible element. *)

Definition bag_eqv (b1 b2: bag) : Prop :=
  forall n, count n b1 = count n b2. 

(** **** Exercise: 2 stars, standard (bag_eqv_properties) *)

(* It is easy to prove [bag_eqv] is an equivalence relation. *)

Lemma bag_eqv_refl : forall b, bag_eqv b b.
Proof.
  unfold bag_eqv. intros. reflexivity.
  Qed.

Lemma bag_eqv_sym: forall b1 b2, bag_eqv b1 b2 -> bag_eqv b2 b1. 
Proof.
  unfold bag_eqv. intros. rewrite H. reflexivity.
  Qed.

Lemma bag_eqv_trans: forall b1 b2 b3, bag_eqv b1 b2 -> bag_eqv b2 b3 -> bag_eqv b1 b3.
Proof.
  unfold bag_eqv. intros. rewrite H. rewrite H0. reflexivity.
  Qed.

(** The following little lemma is handy in a couple of places. *)

Lemma bag_eqv_cons : forall x b1 b2, bag_eqv b1 b2 -> bag_eqv (x::b1) (x::b2).
Proof.
  unfold bag_eqv. intros. simpl. rewrite H. reflexivity.
  Qed.
  
(** [] *)

(* ################################################################# *)
(** * Correctness *)

(** A sorting algorithm must rearrange the elements into a list that
    is totally ordered.  But let's say that a different way: the
    algorithm must produce a list _with the same multiset of values_,
    and this list must be totally ordered. *)

Definition is_a_sorting_algorithm' (f: list nat -> list nat) :=
  forall al, bag_eqv al (f al) /\ sorted (f al).

(** **** Exercise: 3 stars, standard (insert_bag)

    First, prove the auxiliary lemma [insert_bag], which will be
    useful for proving [sort_bag] below.  Your proof will be by
    induction.  *)

Lemma insert_bag: forall x l, bag_eqv (x::l) (insert x l).
Proof.
  intros. induction l.
  +simpl. apply bag_eqv_refl.
  +simpl. bdestruct(x<=?a).
   -apply bag_eqv_refl.
   -unfold bag_eqv. intros. simpl.
   bdestruct(x=?n).
   *bdestruct(a=?n).
    ++lia.
    ++simpl. subst. unfold bag_eqv in IHl. specialize IHl with n. rewrite<-IHl.
    simpl. rewrite Nat.eqb_refl. reflexivity.
   *simpl. assert(count n l =count n (insert x l)).
    {
      unfold bag_eqv in IHl. specialize IHl with n. rewrite<-IHl. simpl. rewrite<- Nat.eqb_neq in H0.
      rewrite H0. reflexivity.
    }
    rewrite H1. reflexivity.
Qed.
(** [] *)

(** **** Exercise: 2 stars, standard (sort_bag)

    Now prove that sort preserves bag contents. *)
Theorem sort_bag: forall l, bag_eqv l (sort l).
  intro l.
  induction l; intro n.
  - reflexivity.
  - simpl. 
    rewrite <- insert_bag.
    simpl.
    rewrite <- (IHl n).
    reflexivity.
Qed.
(** Now we wrap it all up.  *)

Theorem insertion_sort_correct:
  is_a_sorting_algorithm' sort.
Proof.
split. apply sort_bag. apply sort_sorted.
Qed.

(** **** Exercise: 1 star, standard (permutations_vs_multiset)

    Compare your proofs of [insert_perm, sort_perm] with your proofs
    of [insert_bag, sort_bag].  Which proofs are simpler?

      - [ ] easier with permutations,
      - [ ] easier with multisets
      - [ ] about the same.

   Regardless of "difficulty", which do you prefer / find easier to
   think about?
      - [ ] permutations or
      - [ ] multisets

   Put an X in one box in each list. *)
(* Do not modify the following line: *)
Definition manual_grade_for_permutations_vs_multiset : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Permutations and Multisets *)

(** The two specifications of insertion sort are equivalent.  One
    reason is that permutations and multisets are closely related.
    We're going to prove:

       [Permutation al bl <-> bag_eqv al bl.] *)

(** **** Exercise: 3 stars, standard (perm_bag)

    The forward direction is straighforward, by induction on the evidence for
    [Permutation]: *)
Lemma perm_bag:
  forall al bl : list nat,
   Permutation al bl -> bag_eqv al bl. 
Proof.
    intros al bl H n.
    induction H.
    - reflexivity.
    - simpl. rewrite IHPermutation. reflexivity.
    - simpl. lia.
    - rewrite IHPermutation1, IHPermutation2.
      reflexivity.
Qed.

(** The other direction,
    [bag_eqv al bl -> Permutation al bl],
    is surprisingly difficult.  
    This proof approach is due to Zhong Sheng Hu.
    The first three lemmas are used to prove the fourth one. *)

(** **** Exercise: 2 stars, advanced (bag_nil_inv) *)
Lemma bag_nil_inv : forall b, bag_eqv [] b -> b = []. 
Proof.
  intros b.
  induction b; simpl; intro H.
  - reflexivity.
  - exfalso.
    specialize (H a).
    simpl in H.
    rewrite -> Nat.eqb_refl in H.
    discriminate H.
Qed.

(** **** Exercise: 3 stars, advanced (bag_cons_inv) *)
Lemma bag_cons_inv : forall l x n,
    S n = count x l ->
    exists l1 l2,
      l = l1 ++ x :: l2
      /\ count x (l1 ++ l2) = n.
Proof.
  intro l.
  induction l; simpl; intros x n Hcount.
  - discriminate Hcount.
  - bdestruct (a =? x); subst.
    + exists nil, l.
      split; 
        try reflexivity; 
        try (simpl; lia).
    + simpl in Hcount.
      destruct (IHl x n Hcount) as [l1 [l2 [ Heq Hcnt]]].
      exists (a :: l1), l2.
      split.
      * simpl. rewrite <- Heq. reflexivity.
      * simpl. rewrite Hcnt.
        assert (G: a =? x = false). {
          bdestruct (a =? x); subst.
          - exfalso. apply H. reflexivity.
          - reflexivity.
        }
        rewrite G. reflexivity.
Qed.

(** **** Exercise: 2 stars, advanced (count_insert_other) *)
Lemma count_distr: forall l1 l2 x, 
  count x (l1 ++ l2) = count x l1 + count x l2.
Proof.
  intro l1.
  induction l1; simpl; intros l2 x.
  - reflexivity.
  - bdestruct (a =? x); rewrite IHl1; lia.
Qed.
Lemma count_insert_other : forall l1 l2 x y,
    y <> x -> count y (l1 ++ x :: l2) = count y (l1 ++ l2).
Proof.
  intros l1 l2 x y Hneq.
  change (l1 ++ x :: l2) with (l1 ++ [x] ++ l2).
  repeat (rewrite count_distr).
  assert (G: count y [x] = 0). {
    simpl. bdestruct (x =? y).
    - exfalso. apply Hneq. symmetry. assumption.
    - reflexivity.
  }
  rewrite G. lia.
Qed.

(** **** Exercise: 3 stars, advanced (bag_perm) *)
Lemma bag_perm:
  forall al bl, bag_eqv al bl -> Permutation al bl.
  Proof.
    intros al.
    induction al; simpl; intros bl H.
    - apply bag_nil_inv in H. subst. constructor.
    - assert (G: exists l1 l2, bl = l1 ++ a :: l2 /\ count a (l1 ++ l2) = count a al). {
        specialize (H a). simpl in H. rewrite -> Nat.eqb_refl in H. simpl in H.
        apply bag_cons_inv in H.
        assumption.
      }
      destruct G as [l1 [l2 [ Heq Hcnt]]].
      subst.
      apply perm_trans with (a :: (l1 ++ l2)).
      + apply perm_skip.
        apply IHal.
        intro n.
        specialize (H n).
        rewrite count_distr in *.
        simpl in H.
        bdestruct (a =? n); lia.
      + change (a :: l1 ++ l2) with ([a] ++ l1 ++ l2).
        change (l1 ++ a :: l2) with (l1 ++ [a] ++ l2).
        rewrite (app_assoc l1 [a]).
        rewrite (Permutation_app_comm l1 [a]).
        rewrite (app_assoc).
        apply Permutation_refl.
  Qed.
  

(* ################################################################# *)
(** * The Main Theorem: Equivalence of Multisets and Permutations *)
Theorem bag_eqv_iff_perm:
  forall al bl, bag_eqv al bl <-> Permutation al bl.
Proof.
  intros. split. apply bag_perm. apply perm_bag.
Qed.

(** Therefore, it doesn't matter whether you prove your sorting
    algorithm using the Permutations method or the multiset method. *)

Corollary sort_specifications_equivalent:
    forall sort, is_a_sorting_algorithm sort <->  is_a_sorting_algorithm' sort.
Proof.
  unfold is_a_sorting_algorithm, is_a_sorting_algorithm'.
  split; intros;
  destruct (H al); split; auto;
  apply bag_eqv_iff_perm; auto.
Qed.

(** $Date$ *)

(* 2023-08-23 11:34 *)
