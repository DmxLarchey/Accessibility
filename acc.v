(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Utf8.

(** Study on the accessibility predicate:

    1) first we study the type of Acc (acc_i herein)
       be comparing it to the classical characterization
       of accessibility
    2) then we study the type and the code of two recursors 
          - acc_i_rect, the partially dependent recursor
          - acc_i_drect, the fully dependent recursor
    3) we show that all accessibility proofs for x, though
       not provably equal, are heretidarily equivalent.
    4) we finish by instanciating to a measure based recursor
*)

Section accessibility.

  (* Symbols : → ¬ ∃ ∧ ∀  *)

  Variable (X : Type) (R : X → X → Prop).

  (* Infix notation for R *)
  Infix "≺" := R (at level 70).

  (* The classical definition of ≺-accessible elements, ie those which
     do *not* start a infinite ≺-decreasing sequence *)
  Definition acc_c x := ¬ ∃ ρ : nat → X, x = ρ 0 ∧ ∀n, ρ (S n) ≺ ρ n.

  (* acc_c is closed under the following rule

          ∀y, y ≺ x → acc_c y 
        ----------------------- [acc_c_intro]
              acc_c x
  *)

  Fact acc_c_intro x : (∀y, y ≺ x → acc_c y) → acc_c x.
  Proof.
    intros Hx (ρ & -> & HS).
    apply (Hx (ρ 1)).
    + apply HS.
    + exists (λ n, ρ (S n)); eauto.
  Qed.

  (* Associated with Coq inductive types come 
     constructors and recursors:

     - constructors (programming terminology) correspond to
       introduction rules (natural deduction terminology)
     - recursors (programming terminology) correspond to
       elimination rules (natural deduction terminology)

     For eg the type nat, the constructors are O : nat and 
     S : nat -> nat, and the recursor is:

      nat_rect : ∀ P : nat → Type, 
                      P 0 
                    → (∀n, P n → P (S n)) 
                    → ∀n, P n

     Notice that nat_rect states that nat is the smallest
     type closed under the rules:

                           n : nat
           ---------     -----------
            0 : nat       S n : nat

     which are preciselly the constructors of nat.

     There are specialized versions for the sorts Set, Prop
     and SProp (instead of Type above), ie nat_rec, nat_ind 
     and nat_sind but nat_rect can always be used in place of 
     those specialized recursors. We only discuss _rect recursors 
     herein.

     While constructors are *primitive* in Coq, recursors
     are not (contrary to MLTT). They are derived from the
     more general combination of (structural) fixpoints and 
     dependent pattern matching.

     The Inductive commands defines inductive types, ie constructors 
     and automatically generates recursors. Sometimes, these recursors 
     are adequate (powerfull enough like eg nat_rect), but sometimes 
     they are too weak (typically with mutual or nested inductive
     types).

     We block the generation of recursors/eliminations
     rules with the following command, because we *do want* 
     to study them by hand *)

  Unset Elimination Schemes.

  (* This an *exact copy* of Acc from Coq standard library
     which is auto-loaded but we make a copy to study it
     w/o interfering with the default code (autoloaded by 
     the Init module) *)

  Inductive acc_i x : Prop := 
    | acc_i_intro : (∀y, y ≺ x → acc_i y) → acc_i x.

  (* The inversion principle (or destructor) proceeds by
     pattern matching on ax : acc_i x 

     Notice the {_} which specify *implicit* arguments *)
  Definition acc_i_inv {x} (ax : acc_i x) : ∀{y}, y ≺ x → acc_i y :=
    match ax with acc_i_intro _ hx => hx end.

  Section acc_i_rect.

    (* The acc_i_rect recursor expresses that acc_i is
       the *smallest* predicate closed for its introduction
       rule.

       Notice that for inductive predicates over the sort
       Prop (eg Acc), Coq does not generates recursors 
       dependent on the proof term, here acc_i x. It can
       be obtained via the Scheme command though. 
       See below for a handmade fully dependent recursor. 
     *)

    Variables (P : X → Type)
              (Pclosed : ∀x, (∀y, y ≺ x → P y) → P x).

    (* acc_i is smaller than P*)
    Fixpoint acc_i_rect_ltac x (ax : acc_i x) { struct ax } : P x.
    Proof.
      destruct ax as [ hx ].
      apply Pclosed.
      intros.
      apply acc_i_rect_ltac, hx, H.
    Qed.

    Fixpoint acc_i_rect_code x (ax : acc_i x) { struct ax } : P x :=
      match ax with
      | acc_i_intro _ hx => Pclosed _ (λ y hy, acc_i_rect_code y (hx y hy))
      end.

    (* The code are nearly the same upto eta-expansion in the tactic version,
       caused by the destruct tactic *)
    Print acc_i_rect_ltac.
    Print acc_i_rect_code.

  End acc_i_rect.

  (* The shape below just states again that acc_i is the smallest
     predicate close under the rule 

           ∀y, y ≺ x → P y
         -------------------
                P x
  *)
  Definition acc_i_rect (P : X → Type) :
         (∀x, (∀y, y ≺ x → P y) → P x)
        → ∀x, acc_i x → P x.
  Proof. exact (acc_i_rect_code P). Qed.

  (* Because acc_i is the smallest predicate closed for its introduction rule,
     it is smaller than acc_c *)

  (* The "induction 1" below proceed by induction on the first unnamed argument,
     hence of type acc_i x, "using" the specified induction principle acc_i_rect *)
  Fact acc_i_acc_c_ltac : ∀x, acc_i x → acc_c x.
  Proof.
    induction 1 as [ x IHx ] using acc_i_rect.
    apply acc_c_intro, IHx.
  Qed.

  Definition acc_i_acc_c_code : ∀x, acc_i x → acc_c x :=
    acc_i_rect acc_c (λ x hx, acc_c_intro x hx).

  (* Notice that the converse inclusion, ie acc_c x → acc_i x
     *cannot* be proved constructivelly. Thierry Coquand gives
     the following interpretation of why this does not hold
     constructivelly, see "About Brouwer’s Fan Theorem".

     In the (classical) acc_c characterization

          ¬ ∃ρ, x = ρ 0 ∧ ∀n, ρ (S n) ≺ ρ n

     the ∃ quantification is over ρ : nat → X, the type
     of "functions". There are interpretations of the function
     space nat → X which does not cover all possible sequences
     of values in X, because functions must be given by "laws"
     (eg a lambda-term). However, the acc_i characterization
     covers all possible infinite decreasing sequences, even 
     those which are not governed by laws. *)

  (* The acc_i_rect recursors is not the most general recursor
     because the predicate P does not depend on the proof 
     of acc_i x. We thus give a more powerful recursor *)

  Section acc_i_drect.

    (* We can allow P to depend on the proof of acc_i x. The new
       recursor acc_i_drect has proof terms similar to the less 
       dependent version acc_i_rect above *)
    Variables (P : ∀x, acc_i x → Type)
              (Pclosed : ∀x (hx : ∀y, y ≺ x → acc_i y), (∀y (hy : y ≺ x), P y (hx y hy)) → P x (acc_i_intro x hx)).

    Fixpoint acc_i_drect_ltac x (ax : acc_i x) { struct ax } : P x ax.
    Proof.
      destruct ax as [ hx ].
      apply Pclosed.
      intros; apply acc_i_drect_ltac.
    Qed.

    Fixpoint acc_i_drect_code x (ax : acc_i x) { struct ax } : P x ax :=
      match ax with
      | acc_i_intro _ hx => Pclosed _ hx (λ y hy, acc_i_drect_code y (hx y hy))
      end.

    Definition acc_i_drect := acc_i_drect_code.

  End acc_i_drect.

  (* The type of acc_i_drect is not the most readable, so let us formulate
     an equivalent recursor with a cleaner type *)

  Section acc_i_drect'.

    Variables (P : ∀x, acc_i x → Type)
              (Pclosed : ∀x (ax : acc_i x), (∀y (hy : y ≺ x), P y (acc_i_inv ax hy)) → P x ax).

    Fact acc_i_drect'_ltac : ∀x (ax : acc_i x), P x ax.
    Proof.
      induction ax as [ x hx ihx ] using acc_i_drect.
      apply Pclosed, ihx.
    Qed.
   
    Fixpoint acc_i_drect'_code x (ax : acc_i x) { struct ax } :  P x ax :=
      Pclosed x ax (λ y hy, acc_i_drect'_code y (acc_i_inv ax hy)).

  End acc_i_drect'.

  (* The shape below explain the meaning of the type of acc_i_drect' and
     can be read in the context of the "apply" tactic. Given a goal 

       ∀x (ax : acc_i x), P x ax

     after "apply acc_i_drect'", this goal is replaced with

       ∀x (ax : acc_i x), (∀y (hy : y ≺ x), P y (acc_i_inv ax hy)) → P x ax

     meaning that to build "P x ax", it can be further assumed that "P y ay" is 
     already available (induction hypothesis) for any y below x, witnessed
     by "hy : y ≺ x", using the accessibility proof for y contained into
     that of ax : acc_i x, ie the sub-proof "ay := acc_i_inv ax hy" *)

  Definition acc_i_drect' (P : ∀x, acc_i x → Type) :
         (∀x (ax : acc_i x), (∀y (hy : y ≺ x), P y (acc_i_inv ax hy)) → P x ax)
        → ∀x (ax : acc_i x),                                            P x ax.
  Proof. exact (acc_i_drect'_code P). Qed.

  Reserved Notation "x ~~ y" (at level 70, no associativity, format "x  ~~ y").
  
  (* acc_i x proofs are not unique but they are all hereditarilly equivalent *)
  Inductive acc_i_equiv : ∀x, acc_i x → acc_i x → Type :=
    | acc_i_equiv_intro x hx hx' : (∀y hy,  hx y hy ~~ hx' y hy) 
                                 → acc_i_intro x hx ~~ acc_i_intro x hx'
  where "ax ~~ bx" := (acc_i_equiv _ ax bx).

  (* The fully dependent recursor acc_i_drect is needed here, acc_i_rect is
     not enough *)
  Fact acc_i_equiv_total x (ax ax' : acc_i x) : ax ~~ ax'.
  Proof.
    revert ax'; induction ax as [ x hx ihx ] using acc_i_drect; intros [ hx' ].
    constructor; simpl; trivial.
  Qed.

End accessibility.

Arguments acc_i {X} R x.

(** Constructive well foundedness and transfinite recursion *)

(* A well-founded relation is where all member are accessible *)
Definition wf {X} (R : X → X → Prop) := ∀x ,acc_i R x.

Section transfinite_recursion.

  (* From acc_i_rect, we get a transfinite recursor *)

  Variables (X : Type) 
            (R : X → X → Prop) (Rwf : wf R)
            (P : X → Type) (HP : ∀x, (∀y, R y x → P y) → P x).

  Fact transfinite_recursion : ∀x, P x.
  Proof.
    intros x; generalize (Rwf x).
    induction 1 as [ x IHx ] using acc_i_rect.
    apply HP, IHx.
  Qed.

End transfinite_recursion.

Arguments transfinite_recursion {X R}.

Section wf_inverse_image.

  (* acc_i and wf transport along reverse maps 
     (or more generally, surjective morphisms) *)

  Variables (X Y : Type) (f : X → Y) (R : Y → Y → Prop).

  Let acc_i_inv_image_rec y : acc_i R y → ∀ x, y = f x → acc_i (λ u v, R (f u) (f v)) x.
  Proof.
    induction 1 as [ y IHy ] using acc_i_rect; intros x ->.
    constructor. 
    intros x' H'. 
    apply (IHy _ H' _ eq_refl).
  Qed.

  Fact acc_i_inv_image x (ax : acc_i R (f x)) : acc_i (λ u v, R (f u) (f v)) x.
  Proof. exact (acc_i_inv_image_rec (f x) ax _ eq_refl). Qed.

  Fact wf_inverse_image : wf R → wf (λ u v, R (f u) (f v)).
  Proof. intros H x; apply acc_i_inv_image, H. Qed.

End wf_inverse_image.

(* A small application *)

Require Import Arith.

Fact lt_wf_rec m : ∀n, n ≤ m → acc_i (λ u v, u < v) n.
Proof.
  induction m as [ | m IHm ]; intros n Hn; constructor; intros k Hk.
  + exfalso; apply (Nat.nlt_0_r k), (lt_le_trans _ _ _ Hk Hn). 
  + now apply IHm, le_S_n, le_trans with n.
Qed.

(* The _ < _ : nat → nat → Prop relation if well founded *)
Theorem lt_wf : wf (λ u v, u < v).
Proof. exact (λ n, lt_wf_rec _ _ (le_n n)). Qed.

Section induction_on_a_measure.

  (* From transfinite recursion and lt_wf, we derive
     a recursor using a measure in the type nat *)

  Variables (X : Type) (m : X → nat) (P : X → Type).

  Let R x y := m x < m y.
  Let Rwf : wf R.
  Proof. unfold R; apply wf_inverse_image, lt_wf. Qed.
  
  Fact measure_induction :
        (∀x, (∀y, m y < m x → P y) → P x)
       → ∀x,                         P x.
  Proof.
    intros HP x.
    induction x as [ x IHx ] using (transfinite_recursion Rwf).
    apply HP, IHx.
  Qed.

End induction_on_a_measure.





  
