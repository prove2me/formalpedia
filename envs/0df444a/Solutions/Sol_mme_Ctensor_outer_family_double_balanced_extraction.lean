-- Prove2me | solution 1 for mme_Ctensor_outer_family_double_balanced_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T05:07:48.299522+00:00
-- url     : https://prove2.me/submissions/5f58c326-d4f4-4557-b2e0-14d3fd157de0

import Mathlib.Data.Fintype.Card
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Definitions.Def_mme_rank_bridge
import Theorems.Thm_mme_balanced_bigAdd_finite_MM_extractions
import Theorems.Thm_mme_Ctensor_three_balanced_cyclic_induced_matching_extraction
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Theorems.Thm_mme_restrict_kronPow

open MME BigOperators

universe u

namespace CTensorOuterFamilyDoubleBalanced

/-- Distribute the three cyclic factors of a direct sum.  At the tensor
isomorphism quotient this is the ordinary identity
`(∑ Xₐ) (∑ πX_b) (∑ π²X_c) = ∑ Xₐ πX_b π²X_c`. -/
theorem outerTripleDistribution
    {K : Type u} [Field K]
    {A : ℕ} (star : Fin A → TensorObj K 3) :
    let I := Fin A × Fin A × Fin A
    let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
    let block : Fin (Fintype.card I) → TensorObj K 3 := fun j =>
      let p := e.symm j
      threeStarCyclicProduct (star p.1) (star p.2.1) (star p.2.2)
    TensorObj.Restrict (TensorObj.bigAdd block)
      (cyclicSymmetrization (TensorObj.bigAdd star)) := by
  classical
  dsimp only
  let I := Fin A × Fin A × Fin A
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let block : Fin (Fintype.card I) → TensorObj K 3 := fun j =>
    let p := e.symm j
    threeStarCyclicProduct (star p.1) (star p.2.1) (star p.2.2)
  apply ((TensorQ.toQ_eq_iff).mp ?_).1
  rw [TensorQ.toQ_bigAdd, cyclicSymmetrization_eq_public_perm,
    TensorQ.toQ_kron, TensorQ.toQ_kron, TensorQ.toQ_bigAdd]
  have hperm1 :
      TensorQ.toQ (TensorObj.permObj cyclicPerm (TensorObj.bigAdd star)) =
        ∑ a, TensorQ.toQ (TensorObj.permObj cyclicPerm (star a)) := by
    calc
      TensorQ.toQ (TensorObj.permObj cyclicPerm (TensorObj.bigAdd star)) =
          TensorQ.permAut cyclicPerm
            (TensorQ.toQ (TensorObj.bigAdd star)) := by
              rw [TensorQ.permAut_toQ]
      _ = TensorQ.permAut cyclicPerm
            (∑ a, TensorQ.toQ (star a)) := by
              rw [TensorQ.toQ_bigAdd]
      _ = ∑ a, TensorQ.toQ (TensorObj.permObj cyclicPerm (star a)) := by
              simp
  have hperm2 :
      TensorQ.toQ
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (TensorObj.bigAdd star)) =
        ∑ a, TensorQ.toQ
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (star a)) := by
    calc
      TensorQ.toQ
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
            (TensorObj.bigAdd star)) =
          TensorQ.permAut (cyclicPerm.trans cyclicPerm)
            (TensorQ.toQ (TensorObj.bigAdd star)) := by
              rw [TensorQ.permAut_toQ]
      _ = TensorQ.permAut (cyclicPerm.trans cyclicPerm)
            (∑ a, TensorQ.toQ (star a)) := by
              rw [TensorQ.toQ_bigAdd]
      _ = ∑ a, TensorQ.toQ
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (star a)) := by
              simp
  rw [hperm1, hperm2]
  calc
    (∑ j : Fin (Fintype.card I), TensorQ.toQ (block j)) =
        ∑ p : I, TensorQ.toQ
          (threeStarCyclicProduct (star p.1) (star p.2.1) (star p.2.2)) := by
      symm
      apply Fintype.sum_equiv e
      intro p
      simp only [block, Equiv.symm_apply_apply]
    _ = ∑ a : Fin A, ∑ b : Fin A, ∑ c : Fin A,
        TensorQ.toQ (star a) *
          (TensorQ.toQ (TensorObj.permObj cyclicPerm (star b)) *
            TensorQ.toQ
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (star c))) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro b hb
      apply Finset.sum_congr rfl
      intro c hc
      simp only [threeStarCyclicProduct, TensorQ.toQ_kron]
    _ = (∑ a : Fin A, TensorQ.toQ (star a)) *
        ((∑ b : Fin A,
            TensorQ.toQ (TensorObj.permObj cyclicPerm (star b))) *
          (∑ c : Fin A,
            TensorQ.toQ
              (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (star c)))) := by
      simp_rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]

end CTensorOuterFamilyDoubleBalanced

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (hA : 0 < A) (hH : 0 < H) (m : ℕ) :
    let n : ℕ := A ^ 3
    let r : ℕ := H * m
    let R : ℕ := n * r
    let Wouter : ℕ :=
      Nat.card
        {w : Fin R → Fin n // ∀ p,
          Fintype.card {j // w j = p} = r}
    let Winner : ℕ :=
      Nat.card
        {w : Fin r → Fin H // ∀ h,
          Fintype.card {j // w j = h} = m}
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
        ((cyclicSymmetrization T).kronPow R) ∧
      (Wouter : ℝ) *
          (((Winner : ℝ) ^ 2 *
              Real.exp
                (-100 * Real.sqrt
                  (Real.log (((Winner + 1 : ℕ) : ℝ))))) ^ n) ≤
        (k : ℝ) ∧
      (∀ i, a i * b i * c i = volume ^ (3 * R)) := by
  classical
  dsimp only
  let I := Fin A × Fin A × Fin A
  let n : ℕ := Fintype.card I
  let e : I ≃ Fin n := Fintype.equivFin I
  let r : ℕ := H * m
  let R : ℕ := n * r
  let Wouter : ℕ :=
    Nat.card
      {w : Fin R → Fin n // ∀ p,
        Fintype.card {j // w j = p} = r}
  let Winner : ℕ :=
    Nat.card
      {w : Fin r → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}
  let block : Fin n → TensorObj K 3 := fun j =>
    let p := e.symm j
    threeStarCyclicProduct
      (stars.star p.1) (stars.star p.2.1) (stars.star p.2.2)
  let L : ℝ :=
    (Winner : ℝ) ^ 2 *
      Real.exp
        (-100 * Real.sqrt
          (Real.log (((Winner + 1 : ℕ) : ℝ))))
  have hn : 0 < n := by
    dsimp [n]
    apply Fintype.card_pos_iff.mpr
    exact ⟨((⟨0, hA⟩, ⟨0, hA⟩, ⟨0, hA⟩) : I)⟩
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  have hextract : ∀ p : Fin n,
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((block p).kronPow r) ∧
        L ≤ (k : ℝ) ∧
        (∀ i, a i * b i * c i = volume ^ (3 * r)) := by
    intro j
    let p := e.symm j
    obtain ⟨k, a, b, c, hrestrict, hk, hvolume⟩ :=
      mme_Ctensor_three_balanced_cyclic_induced_matching_extraction
        (stars.certificate p.1)
        (stars.certificate p.2.1)
        (stars.certificate p.2.2)
        hH m
    refine ⟨k, a, b, c, ?_, ?_, ?_⟩
    · simpa [block, p, r] using hrestrict
    · simpa [L, Winner, r] using hk
    · simpa [r] using hvolume
  obtain ⟨k, a, b, c, hrestrict, hk, hvolume⟩ :=
    mme_balanced_bigAdd_finite_MM_extractions
      block L hn hL hextract
  have hdist :
      TensorObj.Restrict (TensorObj.bigAdd block)
        (cyclicSymmetrization (TensorObj.bigAdd stars.star)) := by
    simpa [I, n, e, block] using
      CTensorOuterFamilyDoubleBalanced.outerTripleDistribution stars.star
  have hsource :
      TensorObj.Restrict (TensorObj.bigAdd block) (cyclicSymmetrization T) :=
    TensorObj.Restrict.trans hdist
      (mme_cyclicSymmetrization_mono_restrict stars.restrict)
  have hsourcePow :
      TensorObj.Restrict ((TensorObj.bigAdd block).kronPow R)
        ((cyclicSymmetrization T).kronPow R) :=
    mme_restrict_kronPow hsource R
  have hcard : n = A ^ 3 := by
    dsimp [n, I]
    simp [pow_three]
  refine ⟨k, a, b, c, ?_, ?_, ?_⟩
  · simpa [R, r, hcard, mul_assoc] using
      TensorObj.Restrict.trans hrestrict hsourcePow
  · rw [hcard] at hk
    simpa [r, R, Wouter, Winner, L, mul_assoc] using hk
  · intro i
    calc
      a i * b i * c i = (volume ^ (3 * r)) ^ n := hvolume i
      _ = volume ^ ((3 * r) * n) := (pow_mul volume (3 * r) n).symm
      _ = volume ^ (3 * (A ^ 3 * (H * m))) := by
        congr 1
        simp [r, hcard, mul_assoc, mul_comm, mul_left_comm]
