From mathcomp Require Export ssreflect.
Require Export Classical.




Definition set T := T -> Prop.

Definition In {T : Type} (x : T)(X : set T) := X x. 
Notation "x ∈ X" := (@In _ x X )(at level 60).


Definition setU {T : Type} (A B : set T) : set T := 
    fun x => x ∈ A \/ x ∈ B .
Definition setI {T : Type} (A B : set T) : set T := 
    fun x => x ∈ A /\ x ∈ B.
Definition subset {T : Type} (A B : set T) : Prop := 
    forall x, x ∈ A -> x ∈ B.
Definition setD {T : Type} (A B : set T) : set T 
    := fun x => x ∈ A /\ ~ x ∈ B.
Definition setC {T : Type} (A : set T) : set T 
    := fun x => ~ x ∈ A.
Definition set0 {T : Type} : set T := 
    fun _ : T => False.



Notation "A ∩ B" := (@setI _ A B)(at level 40).
Notation "A ∪ B" := (@setU _ A B)(at level 40).
Notation "A ⊂ B" := (@subset _ A B)(at level 30).
Notation "A // B" := (@setD _ A B)(at level 40).
Notation "¬ A" := (@setC _ A)(at level 40).
Notation "∅" := set0.

Axiom extension : forall {T : Type} (A B : set T),
    A ⊂ B /\ B ⊂ A -> A = B.



Section SetsFacts.

Context  {T : Type}.


Theorem setCU (A B : set T):
    ¬ (A ∪ B) = ¬ A ∩ ¬ B.
Proof.
    apply extension; split => x Hx.
    +   split => F; apply Hx; [left|right] => //.
    +   move : Hx => [Ha_ Hb_].
        move => [Ha|Hb]; [apply Ha_ | apply Hb_] => //.
Qed.

Theorem setCI (A B : set T):
    ¬ (A ∩ B) = ¬ A ∪ ¬ B.
Proof.
    apply extension; split => x Hx.
    +   apply NNPP => F.
        rewrite /setC /setU /In /= in F.
        move /not_or_and : F => [/NNPP HA /NNPP NB ].
        apply Hx; split => //.
    +   move => [HA HB].
        move : Hx => [H|H]; apply H => //.
Qed.        