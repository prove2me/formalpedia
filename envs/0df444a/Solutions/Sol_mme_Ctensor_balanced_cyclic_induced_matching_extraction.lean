-- Prove2me | solution 1 for mme_Ctensor_balanced_cyclic_induced_matching_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:48:13.669857+00:00
-- url     : https://prove2.me/submissions/e8165f3b-afaf-4542-97c7-0e618266ccee

import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_Ctensor_balanced_cyclic_induced_family_realization
import Theorems.Thm_mme_Ctensor_balanced_word_card
import Theorems.Thm_mme_MM_support_behrend_induced_matching
import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {H volume : ℕ}
    (cert : CTensorOneHOneCertificate T H volume)
    (hH : 0 < H) (m : ℕ) :
    let R : ℕ := H * m
    let W : ℕ :=
      Nat.card
        {w : Fin R → Fin H // ∀ h,
          Fintype.card {j // w j = h} = m}
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
        ((cyclicSymmetrization T).kronPow R) ∧
      ((W : ℝ) ^ 2 *
          Real.exp
            (-100 * Real.sqrt
              (Real.log (((W + 1 : ℕ) : ℝ))))) ≤
        (k : ℝ) ∧
      (∀ i, a i * b i * c i = volume ^ (3 * R)) := by
  classical
  dsimp only
  let R : ℕ := H * m
  let W : ℕ :=
    Nat.card
      {w : Fin R → Fin H // ∀ h,
        Fintype.card {j // w j = h} = m}
  have hprod : (∏ _h : Fin H, m.factorial) = m.factorial ^ H := by
    simp
  have hsum : (∑ _h : Fin H, m) = H * m := by
    simp
  have hdiv : (∏ _h : Fin H, m.factorial) ∣ (H * m).factorial := by
    have h := Nat.prod_factorial_dvd_factorial_sum
      (Finset.univ : Finset (Fin H)) (fun _ : Fin H ↦ m)
    rw [hsum] at h
    exact h
  have hid : W * m.factorial ^ H = R.factorial := by
    dsimp [W, R]
    rw [mme_Ctensor_balanced_word_card, ← hprod,
      Nat.div_mul_cancel hdiv]
  have hW : 0 < W := by
    by_contra hnot
    have hzero : W = 0 := Nat.eq_zero_of_not_pos hnot
    rw [hzero, zero_mul] at hid
    exact (Nat.factorial_pos R).ne' hid.symm
  obtain ⟨E, hx, hy, hz, hinduced, hcard⟩ :=
    mme_MM_support_behrend_induced_matching W hW
  obtain ⟨a, b, c, hrestrict, hvolume⟩ :=
    mme_Ctensor_balanced_cyclic_induced_family_realization
      cert hH m E hx hy hz hinduced
  refine ⟨E.card, a, b, c, ?_, ?_, ?_⟩
  · simpa [R] using hrestrict
  · simpa [W] using hcard
  · simpa [R] using hvolume
