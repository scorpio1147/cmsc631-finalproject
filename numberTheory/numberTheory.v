From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Module chinese_remainder_playground.
Open Scope Z_scope.

Definition divides (d n : Z) : Prop := 
    exists k, n = d * k.

(* Local Notation "d | n" := (divides d n) (at level 40) : Z_scope. *)

Definition cong_exists (n a b : Z) : Prop := 
    exists k, a = b + n * k.

Definition cong (n a b : Z) : Prop := 
    divides n (a - b).

Lemma conq_exists_equiv_cong :
    forall (n a b : Z), cong n a b <-> cong_exists n a b.
Proof.
    intros n a b. split.
    - intros H. unfold cong in H. unfold divides in H. 
      destruct H as [k H].  unfold cong_exists. exists k. 
      rewrite <- H. lia.
    - intros H. unfold cong_exists in H. destruct H as [k H]. 
      unfold cong. unfold divides. exists k. rewrite H. lia.
Qed. 

Local Notation "a ≡ b [ n ]" := (cong n a b) (at level 40) : Z_scope.

Lemma cong_refl : 
    forall (n a : Z), a ≡ a [ n ].
Proof.
    intros n a. unfold cong. unfold divides. exists 0. lia.
Qed.
    
(* https://rocq-prover.org/doc/V8.12%2Bbeta1/stdlib/Coq.Numbers.Integer.Abstract.ZMul.html *)
(* https://rocq-prover.org/doc/V8.12%2Bbeta1/stdlib/Coq.Numbers.Integer.Abstract.ZAdd.html *)

Lemma cong_sym : 
    forall (n a b : Z), a ≡ b [ n ] <-> b ≡ a [ n ].
Proof.
    intros n a b. split; 
    unfold cong; unfold divides; 
    intros H; destruct H as [k H]; 
    exists (-k); rewrite Z.mul_opp_r; 
    rewrite <- H; lia.
Qed.

Lemma cong_trans : 
    forall (n a b c : Z), 
    a ≡ b [ n ] -> b ≡ c [ n ] -> a ≡ c [ n ].
Proof.
    intros n a b c. unfold cong, divides. 
    intros [k1 H1] [k2 H2]. exists (k1 + k2). lia.
Qed.
(* congruence is an equivalence relation! *)

Ltac cong_divides := unfold cong, divides. (* this might be useful later*)

Lemma cong_add : 
    forall (n a b c d : Z),
    a ≡ b [ n ] -> c ≡ d [ n ] -> (a + c) ≡ (b + d) [ n ].
Proof.
    intros n a b c d. cong_divides. 
    intros [k1 H1] [k2 H2]. 
    exists (k1 + k2). lia.
Qed.

Lemma cong_mult : 
    forall (n a b c d : Z),
    a ≡ b [ n ] -> c ≡ d [ n ] -> (a * c) ≡ (b * d) [ n ].
Proof.
    intros n a b c d. cong_divides. 
    intros [k1 H1] [k2 H2]. 
    exists (c * k1 + b * k2). lia.
Qed.

Lemma divides_mult_l :
  forall d n c : Z, divides d n -> divides d (c * n).
Proof.
  intros d n c [k Hk].
  subst n.
  unfold divides.
  exists (c * k). lia.
Qed.

Lemma coprime_divides_factor : (* wait this is just euclid's lemma *)
  forall m n k u v,
    u * m + v * n = 1 ->
    divides n (m * k) ->
    divides n k.
Proof.
  intros m n k u v Hbez [t Ht]. 
  unfold divides.
  exists (u * t + v * k).
  symmetry.
  rewrite Z.mul_add_distr_l.
  rewrite Z.mul_assoc.
  rewrite Z.mul_comm with (m := u) (n := n).
  rewrite <- Z.mul_assoc.
  rewrite <- Ht.
  rewrite Z.mul_assoc. 
  rewrite Z.mul_assoc.
  rewrite Z.mul_comm with (m := v) (n := n).
  rewrite <- Z.mul_add_distr_r.  
  rewrite Hbez. lia.
Qed.

Lemma coprime_mult_divides :
  forall m n d u v,
    u * m + v * n = 1 ->
    divides m d ->
    divides n d ->
    divides (m * n) d.
Proof.
  intros m n d u v Hbez Hmd Hnd.
  destruct Hmd as [k Hk].
  destruct Hnd as [l Hl].
  subst d.
  assert (Hnk : divides n (m * k)).
  unfold divides. exists l. assumption.
  destruct (coprime_divides_factor m n k u v Hbez Hnk).
  subst k.
  unfold divides.
  exists x. lia.
Qed.

Lemma divides_sub_l d a b :
  divides d a -> divides d b ->
  divides d (b - a).
Proof.
  intros [k Ha] [l Hl].
  subst a b.
  exists (l - k). lia.
Qed.

Theorem chinese_remainder_bezout_exists :
  forall (m n a b u v : Z),
    u * m + v * n = 1 ->
    exists x, a ≡ x [ m ] /\ b ≡ x [ n ].
Proof.
  intros m n a b u v Hbez.
  exists (a + (b - a) * u * m); split.
  - unfold cong, divides.
    exists ((a - b) * u). lia.
  - unfold cong, divides.
    apply (cong_sym n ((a + (b - a) * u * m)) b).
    assert (Hinv : divides n (u * m - 1)).
    unfold divides. exists (-v). lia. 
    pose proof (divides_mult_l n (u * m - 1) (b - a) Hinv) as Hdiv.
    destruct Hdiv as [k Hk].
    exists k. lia.
Qed.


Theorem chinese_remainder_bezout_unique :
  forall (m n a b u v x y : Z),
    u * m + v * n = 1 ->
    a ≡ x [ m ] -> b ≡ x [ n ] ->
    a ≡ y [ m ] -> b ≡ y [ n ] ->
    x ≡ y [ m * n ].
Proof.
  intros m n a b u v x y Hbez Hax Hbx Hay Hby.
  assert (Hmx : x ≡ y [ m ]).
  apply (cong_trans m x a y). apply (cong_sym m a x).
  assumption. assumption.
  assert (Hnx : x ≡ y [ n ]).
  apply (cong_trans n x b y). apply (cong_sym n b x).
  assumption. assumption.
  unfold cong in *.
  destruct Hmx as [km Hkm].
  destruct Hnx as [kn Hkn].
  apply (coprime_mult_divides m n (x - y) u v); try assumption.
  assert (x - y = (a - y) - (a - x)). lia. rewrite H. 
  apply divides_sub_l with (d := m) (a := (a - x)) (b := (a - y)); try assumption.
  assert (x - y = (b - y) - (b - x)). lia. rewrite H. 
  apply divides_sub_l with (d := n) (a := (b - x)) (b := (b - y)); try assumption.
Qed.

Definition prime (p : Z) : Prop :=
    p > 1 /\ forall d, divides d p -> d = 1 \/ d = p.

End chinese_remainder_playground.

(*==========================================================================*)

Module gcd_playground.
Open Scope nat_scope.

Definition divides (d n : nat) : Prop := 
    exists k, n = d * k.

Lemma divides_add d x y :
  divides d x -> divides d y -> divides d (x + y).
Proof.
  intros [kx Hx] [ky Hy].
  subst x y. unfold divides.
  exists (kx + ky).
  symmetry.
  apply Nat.mul_add_distr_l.
Qed.

Lemma divides_sub_l d a b :
  a <= b ->
  divides d a -> divides d b ->
  divides d (b - a).
Proof.
  intros Hab [k Ha] [l Hl].
  subst a b.
  exists (l - k).
  rewrite Nat.mul_sub_distr_l. 
  rewrite Nat.mul_comm.
  reflexivity.
Qed.

(* Notation "d | n" := (divides d n) (at level 45) : nat_scope. *)

Inductive is_egcd : nat -> nat -> nat -> Prop :=
  | is_egcd_l0 : forall x : nat, is_egcd x 0 x
  | is_egcd_r0 : forall x : nat, is_egcd x x 0
  | is_egcd_l : forall x a b : nat, is_egcd x a b -> is_egcd x (a + b) b
  | is_egcd_r : forall x a b : nat, is_egcd x a b -> is_egcd x a (a + b)
.

Definition is_gcd (d a b : nat) : Prop :=
    divides d a /\ divides d b /\ 
    forall (d' : nat), divides d' a -> divides d' b -> divides d' d.


Example gcd0 : is_gcd 0 0 0. Proof. 
  unfold is_gcd. split.
   - exists 0. lia.
   - split.
     + exists 0. lia.
     + intros d' A B. apply A.
Qed.

Example egcd : is_egcd 3 9 12. Proof.
  apply is_egcd_r with (x := 3) (a := 9) (b := 3). 
  apply is_egcd_l with (x := 3) (a := 6) (b := 3). 
  apply is_egcd_l with (x := 3) (a := 3) (b := 3). 
  apply is_egcd_l with (x := 3) (a := 0) (b := 3). 
  apply is_egcd_l0.
Qed. 


Example gcdr : forall x : nat, is_gcd x 0 x. Proof. 
  unfold is_gcd. split.
   - exists 0. lia.
   - split.
     + exists 1. lia.
     + intros d' A B. apply B.
Qed.

Example gcdl : forall x : nat, is_gcd x x 0. Proof. 
  unfold is_gcd. split.
   - exists 1. lia.
   - split.
     + exists 0. lia.
     + intros d' A B. apply A.
Qed.

(* Fixpoint gcd (a b : nat) : nat :=
  match a, b with
  | 0, x => x
  | x, 0 => x
  | S a', S b' =>
      if a <=? b
      then gcd a (b - a)
      else gcd (a - b) b
  end. *)

(* above does not work because rocq is not convinced it terminates *)

Fixpoint gcd_iter (n a b : nat) : nat :=
match n with
| 0 => a
| S n' =>
    match a, b with
    | 0, x => x
    | x, 0 => x
    | S a', S b' =>
        if a <=? b
        then gcd_iter n' a (b - a)
        else gcd_iter n' (a - b) b
    end
end.

(* we can fix this by adding a dummy argument that always decreases *)

Definition gcd (a b : nat) : nat := gcd_iter (a + b) a b.

(* a + b should suffice as an upper bound for the number of iterations
   can we prove this? *)

Definition gcd_step (a b : nat) : nat * nat :=
  match a, b with
  | 0, x => (0, x)
  | x, 0 => (x, 0)
  | S a', S b' =>
      if a <=? b
      then (a, b - a)
      else (a - b, b)
  end.

Lemma gcd_step_invariant :
  forall d a b,
    a <> 0 -> b <> 0 ->
    is_gcd d a b ->
    let (a', b') := gcd_step a b in
    is_gcd d a' b'.
Proof.
  intros d a b Ha Hb Hg.
  unfold gcd_step.
  destruct a as [|a']; try assumption.
  destruct b as [|b']; try assumption.
  simpl. destruct Hg as [Hda [Hdb Hmax]].
  destruct (Nat.leb_spec0 (S a') (S b')) as [HSab | HSba].
  -  destruct (Nat.leb_spec0 a' b') as [Hab | Hba]. 
    + assert (HbaSba : b' - a' = S b' - S a'). lia.
      assert (Hdb_minus : divides d (b' - a')).
      rewrite HbaSba.
      apply divides_sub_l; try assumption.
      split; try assumption. split; try assumption.
      intros d' HdSa Hdba. apply Hmax in HdSa; try assumption.
      assert (HSaba : S a' + (b' - a') = S b').
      lia. rewrite <- HSaba. 
      apply divides_add with (d:=d') (x := S a') (y := b' - a');
      assumption.
    + unfold not in Hba. assert (HbaSba : S a' <= S b' -> a' <= b'). lia. 
      apply HbaSba in HSab. apply Hba in HSab. destruct HSab.
  - destruct (Nat.leb_spec0 a' b') as [Hab | Hba].
    + unfold not in HSba. assert (HbaSba : a' <= b' -> S a' <= S b'). lia. 
      apply HbaSba in Hab. apply HSba in Hab. destruct Hab.
    + assert (HbaSba : a' - b' = S a' - S b'). lia.
      rewrite HbaSba. split. apply divides_sub_l; try lia; try assumption.
      split; try assumption. intros d' HdSa Hdba. apply Hmax in Hdba; try assumption.
      assert (HSaba : (S a' - S b') + S b' = S a').
      lia. rewrite <- HSaba. 
      apply divides_add with (d := d') (x := S a' - S b') (y := S b');
      assumption.
Qed.

(* the above is kind of like a 'preservation' statement 
   since it shows that the gcd stays the same after each
   transition / iteration *)

Lemma gcd_step_decreases :
  forall a b,
    a <> 0 -> b <> 0 ->
    let (a', b') := gcd_step a b in
    a' + b' < a + b.
Proof.
    intros a b Ha Hb. unfold gcd_step.  
    destruct a as [|a']; try assumption. contradiction.
    destruct b as [|b']; try assumption. contradiction.
    simpl. destruct (Nat.leb_spec0 a' b') as [Hab | Hba]; lia.
Qed.

(* the above is kind of like a 'progress' statement 
   since the a + b argument is always decreasing *)

Lemma divides_refl d :
  d <> 0 -> divides d d.
Proof.
  intros Hd. unfold divides.
  exists 1. lia.
Qed.

Lemma is_gcd_diag a :
  a <> 0 -> is_gcd a a a.
Proof.
  unfold is_gcd.
  split.
  - unfold divides. exists 1. lia.
  - split.
    + unfold divides. exists 1. lia.
    + intros d [k1 H1] [k2 H2]. 
      subst. destruct k1 as [|k1]. lia.
      unfold divides. exists (S k1). reflexivity.
Qed.

Lemma gcd_iter_zero_r :
  forall n a, gcd_iter n a 0 = a.
Proof.
  induction n as [|n IH]; intros a; simpl. 
  reflexivity; simpl; auto.
  destruct a; reflexivity.
Qed.

Lemma gcd_iter_zero_l :
  forall n b, n <> 0 -> gcd_iter n 0 b = b.
Proof.
  induction n as [|n IH]; intros b; simpl; intros H. 
  destruct H; reflexivity. reflexivity.
Qed.

Lemma is_gcd_minus_l_forward :
  forall d a b,
    a <= b ->
    is_gcd d a (b - a) ->
    is_gcd d a b.
Proof.
  intros d a b Hab [Hda [Hdbma Hmax]].
  unfold is_gcd.
  split.
  - assumption.
  - split.
      assert (Hb_eq : b = a + (b - a)). lia.
      rewrite Hb_eq.
      apply divides_add with (d := d); assumption.
      intros d' Hda' Hdb'.
      assert (Hdbma' : divides d' (b - a)).
      apply divides_sub_l with (d := d'); try assumption. 
      apply Hmax; assumption.
Qed.

Lemma is_gcd_minus_l_rev : 
  forall d a b,
    a <= b ->
    is_gcd d a b ->
    is_gcd d a (b - a).
Proof.
  intros d a b  Hab [Hda [Hdbma Hmax]].
  unfold is_gcd.
  split.
  - assumption.
  - split.
      apply divides_sub_l; assumption.
      intros d' Hda' Hdb'.
      apply Hmax; try assumption.
      assert (Haba: a + (b - a) = b). lia. rewrite <- Haba.
      apply divides_add with (d:=d') (x := a) (y := (b-a)); assumption.
Qed.

Lemma is_gcd_minus_l : 
  forall d a b,
  a <= b ->
  (is_gcd d a b) <-> is_gcd d a (b - a).
Proof.
  intros d a b H. split.
  - apply is_gcd_minus_l_rev. assumption.
  - apply is_gcd_minus_l_forward. assumption. 
Qed.

Lemma is_gcd_minus_r_forward :
  forall d a b,
    b <= a ->
    is_gcd d (a - b) b ->
    is_gcd d a b.
Proof.
  intros d a b Hba [Hdam [Hdb Hmax]].
  unfold is_gcd.
  split.
  - assert (Ha_eq : a = (a - b) + b). lia.
    rewrite Ha_eq.
    apply divides_add with (d := d); assumption.
  - split; try assumption.
      intros d' Hda' Hdb'.
      assert (Hdam' : divides d' (a - b)).
      apply divides_sub_l with (d := d') (a := b) (b := a); try assumption.
      apply Hmax; assumption.
Qed.

Lemma is_gcd_minus_r_rev :
  forall d a b,
    b <= a ->
    is_gcd d a b ->
    is_gcd d (a - b) b.
Proof.
  intros d a b Hba [Hdam [Hdb Hmax]].
  unfold is_gcd.
  split.
  - apply divides_sub_l; assumption.
  - split; try assumption.
      intros d' Hda' Hdb'.
      apply Hmax; try assumption.
      assert (Haba: b + (a - b) = a). lia. rewrite <- Haba.
      apply divides_add with (d := d') (x := b) (y := (a-b)); assumption.
Qed.

Lemma is_gcd_minus_r : 
  forall d a b,
  b <= a ->
  (is_gcd d a b) <-> is_gcd d (a - b) b.
Proof.
  intros d a b H. split.
  - apply is_gcd_minus_r_rev. assumption.
  - apply is_gcd_minus_r_forward. assumption. 
Qed.

Lemma is_gcd_0_0_d0 :
  forall d, is_gcd d 0 0 -> d = 0.
Proof.
  intros d [Hd0 [Hd0' Hmax]].
  specialize (Hmax (S d)).
  assert (Hsd0 : divides (S d) 0). exists 0. lia.
  apply Hmax in Hsd0. destruct Hsd0. destruct x; 
  lia. assumption.
Qed.

Lemma is_egcd_implies_is_gcd :
  forall d a b,
  is_egcd d a b -> is_gcd d a b.
Proof.
  intros d a b H. induction H. 
  + apply gcdr.
  + apply gcdl.
  + unfold is_gcd. split.
    - unfold is_gcd in IHis_egcd. destruct IHis_egcd. 
      destruct H1. apply divides_add. assumption. assumption.
    - split.
      * unfold is_gcd in IHis_egcd. 
        destruct IHis_egcd. destruct H1. apply H1.
      * intros d' X Y. apply IHis_egcd. 
        ** assert ((a + b) - b = a). lia. rewrite <- H0. 
            apply divides_sub_l with (a := b) (b := a + b). 
            lia. apply Y. apply X.
        ** apply Y.
  + unfold is_gcd. split.
    - unfold is_gcd in IHis_egcd. 
      destruct IHis_egcd. destruct H1. apply H0.
    - split.
      * unfold is_gcd in IHis_egcd. 
        destruct IHis_egcd. destruct H1. 
        apply divides_add. apply H0. apply H1.
      * intros d' X Y. apply IHis_egcd. 
        ** apply X.
        ** assert ((a + b) - a = b). lia. 
          rewrite <- H0. apply divides_sub_l with (a := a) (b := a + b). 
          lia. apply X. apply Y.
Qed.

Lemma is_gcd_implies_is_egcd :
  forall d a b,
  is_gcd d a b -> is_egcd d a b.
Proof.
  intros d a b H. 
  remember (a + b) as n eqn: Hn. generalize dependent b.
  generalize dependent a. generalize dependent n. 
  induction n as [| n IH].
  - intros a b H Hab. assert (Haab: 0 = a + b -> a = 0 /\ b = 0).
    intros Hba. split; lia. apply Haab in Hab. 
    destruct Hab. subst. clear Haab.
    assert (d = 0). apply is_gcd_0_0_d0. apply H. 
    rewrite H0. apply is_egcd_l0.
  - intros a b H Hab.
Abort. 
(*we need strong induction here, need the result for all n' < S n*)

(*
  51 => 41 => 31 => 21 => 11 => 10

   62 => 42 => 22 => 02
 *)

Lemma gcd_iter_correct :
  forall n a b,
    a <> 0 -> b <> 0 ->
    a + b <= n ->
    is_gcd (gcd_iter n a b) a b.
Proof.
Admitted.

End gcd_playground.
