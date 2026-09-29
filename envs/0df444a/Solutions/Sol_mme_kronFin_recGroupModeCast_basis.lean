-- Prove2me | solution 1 for mme_kronFin_recGroupModeCast_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T08:47:30.440646+00:00
-- url     : https://prove2.me/submissions/8c518e61-54ee-41a5-bcc9-9e6b783fec1c

import Definitions.Def_mme_kronFin_rec_group_position_equiv_data

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

private noncomputable def basisCast
    {K : Type u} [Field K] {d : ℕ} {X Y : TensorObj K d}
    (hX : X = Y) {i : Fin d} {I J : Type u} (hI : I = J)
    (b : Basis I K (X.V i)) : Basis J K (Y.V i) := by
  subst Y
  subst J
  exact b

private theorem basisCast_heq
    {K : Type u} [Field K] {d : ℕ} {X Y : TensorObj K d}
    (hX : X = Y) {i : Fin d} {I J : Type u} (hI : I = J)
    (b : Basis I K (X.V i)) : HEq (basisCast hX hI b) b := by
  subst Y
  subst J
  rfl

private theorem basisCast_apply
    {K : Type u} [Field K] {d : ℕ} {X Y : TensorObj K d}
    (hX : X = Y) {i : Fin d} {I J : Type u} (hI : I = J)
    (b : Basis I K (X.V i)) (x : I) :
    basisCast hX hI b (hI ▸ x) =
      LinearEquiv.cast (R := K)
        (M := fun U : TensorObj K d ↦ U.V i) hX (b x) := by
  subst Y
  subst J
  rfl

private theorem appendBasisLeft
    {K : Type u} [Field K] {d : ℕ} {i : Fin d} :
    ∀ (m n : ℕ) (A : Fin m → TensorObj K d)
      (B : Fin n → TensorObj K d)
      (indexA : Fin m → Type u) (indexB : Fin n → Type u)
      (bA : ∀ r, Basis (indexA r) K ((A r).V i))
      (bB : ∀ r, Basis (indexB r) K ((B r).V i))
      (a : Fin m),
      HEq (TensorObj.recAppendBasisFamily m n A B i indexA indexB bA bB
        (TensorObj.recAppendPositionFrom m n (Sum.inl a))) (bA a)
  | 0, _, _, _, _, _, _, _, a => a.elim0
  | m + 1, n, A, B, indexA, indexB, bA, bB, a => by
      refine Fin.cases ?_ (fun q ↦ ?_) a
      · rfl
      · exact appendBasisLeft m n
          (fun r : Fin m ↦ A r.succ) B
          (fun r : Fin m ↦ indexA r.succ) indexB
          (fun r ↦ bA r.succ) bB q

private theorem appendBasisRight
    {K : Type u} [Field K] {d : ℕ} {i : Fin d} :
    ∀ (m n : ℕ) (A : Fin m → TensorObj K d)
      (B : Fin n → TensorObj K d)
      (indexA : Fin m → Type u) (indexB : Fin n → Type u)
      (bA : ∀ r, Basis (indexA r) K ((A r).V i))
      (bB : ∀ r, Basis (indexB r) K ((B r).V i))
      (q : Fin n),
      HEq (TensorObj.recAppendBasisFamily m n A B i indexA indexB bA bB
        (TensorObj.recAppendPositionFrom m n (Sum.inr q))) (bB q)
  | 0, _, _, B, _, indexB, _, bB, q => by
      change HEq (bB q) (bB q)
      rfl
  | m + 1, n, A, B, indexA, indexB, bA, bB, q =>
      appendBasisRight m n
        (fun r : Fin m ↦ A r.succ) B
        (fun r : Fin m ↦ indexA r.succ) indexB
        (fun r ↦ bA r.succ) bB q

private theorem groupedBasisAtPosition
    {K : Type u} [Field K] {d : ℕ} {i : Fin d} :
    ∀ (k : ℕ) (count : Fin k → ℕ)
      (X : Fin k → TensorObj K d) (index : Fin k → Type u)
      (b : ∀ s, Basis (index s) K ((X s).V i))
      (r : Fin (TensorObj.recGroupLength k count)),
      HEq (TensorObj.recGroupBasisFamily k count X i index b r)
        (b (TensorObj.recGroupPositionEquiv k count r).1)
  | 0, _, _, _, _, r => r.elim0
  | k + 1, count, X, index, b, r => by
      cases h : TensorObj.recAppendPositionTo (count 0)
          (TensorObj.recGroupLength k (fun s ↦ count s.succ)) r with
      | inl a =>
          have hr : TensorObj.recAppendPositionFrom (count 0)
              (TensorObj.recGroupLength k (fun s ↦ count s.succ))
              (Sum.inl a) = r := by
            simpa only [h] using TensorObj.recAppendPositionFrom_to
              (count 0) (TensorObj.recGroupLength k
                (fun s ↦ count s.succ)) r
          have happ := appendBasisLeft
            (count 0) (TensorObj.recGroupLength k (fun s ↦ count s.succ))
            (fun _ ↦ X 0)
            (TensorObj.recGroupFamily k (fun s ↦ count s.succ)
              (fun s ↦ X s.succ))
            (fun _ ↦ index 0)
            (TensorObj.recGroupFamily k (fun s ↦ count s.succ)
              (fun s ↦ index s.succ))
            (fun _ ↦ b 0)
            (TensorObj.recGroupBasisFamily k (fun s ↦ count s.succ)
              (fun s ↦ X s.succ) i (fun s ↦ index s.succ)
              (fun s ↦ b s.succ)) a
          have happ' : HEq
              (TensorObj.recGroupBasisFamily (k + 1) count X i index b r)
              (b 0) := by rw [← hr]; exact happ
          have hpos :
              (TensorObj.recGroupPositionEquiv (k + 1) count r).1 = 0 := by
            unfold TensorObj.recGroupPositionEquiv
            change (TensorObj.sigmaFinSuccEquiv count
              ((Equiv.sumCongr (Equiv.refl _)
                (TensorObj.recGroupPositionEquiv k
                  (fun s ↦ count s.succ)))
                (TensorObj.recAppendPositionTo (count 0)
                  (TensorObj.recGroupLength k
                    (fun s ↦ count s.succ)) r))).1 = 0
            rw [h]
            rfl
          rw [hpos]
          exact happ'
      | inr q =>
          have hr : TensorObj.recAppendPositionFrom (count 0)
              (TensorObj.recGroupLength k (fun s ↦ count s.succ))
              (Sum.inr q) = r := by
            simpa only [h] using TensorObj.recAppendPositionFrom_to
              (count 0) (TensorObj.recGroupLength k
                (fun s ↦ count s.succ)) r
          have happ := appendBasisRight
            (count 0) (TensorObj.recGroupLength k (fun s ↦ count s.succ))
            (fun _ ↦ X 0)
            (TensorObj.recGroupFamily k (fun s ↦ count s.succ)
              (fun s ↦ X s.succ))
            (fun _ ↦ index 0)
            (TensorObj.recGroupFamily k (fun s ↦ count s.succ)
              (fun s ↦ index s.succ))
            (fun _ ↦ b 0)
            (TensorObj.recGroupBasisFamily k (fun s ↦ count s.succ)
              (fun s ↦ X s.succ) i (fun s ↦ index s.succ)
              (fun s ↦ b s.succ)) q
          have happ' : HEq
              (TensorObj.recGroupBasisFamily (k + 1) count X i index b r)
              (TensorObj.recGroupBasisFamily k (fun s ↦ count s.succ)
                (fun s ↦ X s.succ) i (fun s ↦ index s.succ)
                (fun s ↦ b s.succ) q) := by rw [← hr]; exact happ
          have ih := groupedBasisAtPosition k
            (fun s ↦ count s.succ) (fun s ↦ X s.succ)
            (fun s ↦ index s.succ) (fun s ↦ b s.succ) q
          have hpos :
              (TensorObj.recGroupPositionEquiv (k + 1) count r).1 =
                (TensorObj.recGroupPositionEquiv k
                  (fun s ↦ count s.succ) q).1.succ := by
            change (TensorObj.sigmaFinSuccEquiv count
              ((Equiv.sumCongr (Equiv.refl _)
                (TensorObj.recGroupPositionEquiv k
                  (fun s ↦ count s.succ)))
                (TensorObj.recAppendPositionTo (count 0)
                  (TensorObj.recGroupLength k
                    (fun s ↦ count s.succ)) r))).1 = _
            rw [h]
            rfl
          rw [hpos]
          exact happ'.trans ih

theorem solution
    {K : Type u} [Field K] {d k : ℕ} (count : Fin k → ℕ)
    (X : Fin k → TensorObj K d) (i : Fin d)
    (index : Fin k → Type u)
    (b : ∀ s, Basis (index s) K ((X s).V i))
    (r : Fin (TensorObj.recGroupLength k count))
    (x : index (TensorObj.recGroupPositionEquiv k count r).1) :
    let hX : X (TensorObj.recGroupPositionEquiv k count r).1 =
        TensorObj.recGroupFamily k count X r :=
      (TensorObj.recGroupFamily_at_position k count X r).symm
    let hIndex : index (TensorObj.recGroupPositionEquiv k count r).1 =
        TensorObj.recGroupFamily k count index r :=
      (TensorObj.recGroupFamily_at_position k count index r).symm
    LinearEquiv.cast (R := K)
        (M := fun U : TensorObj K d ↦ U.V i) hX (b _ x) =
      TensorObj.recGroupBasisFamily k count X i index b r
        (hIndex ▸ x) := by
  dsimp only
  have hb := groupedBasisAtPosition k count X index b r
  have hX := (TensorObj.recGroupFamily_at_position k count X r).symm
  have hIndex := (TensorObj.recGroupFamily_at_position k count index r).symm
  let b' := basisCast hX hIndex
    (b (TensorObj.recGroupPositionEquiv k count r).1)
  have hb' : HEq b' (b (TensorObj.recGroupPositionEquiv k count r).1) :=
    basisCast_heq hX hIndex _
  have heq : TensorObj.recGroupBasisFamily k count X i index b r = b' :=
    eq_of_heq (hb.trans hb'.symm)
  rw [heq]
  exact (basisCast_apply hX hIndex _ x).symm
