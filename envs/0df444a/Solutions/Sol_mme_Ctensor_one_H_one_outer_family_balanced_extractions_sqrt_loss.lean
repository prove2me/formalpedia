-- Prove2me | solution 1 for mme_Ctensor_one_H_one_outer_family_balanced_extractions_sqrt_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T04:58:58.810188+00:00
-- url     : https://prove2.me/submissions/e655d525-6feb-49dc-b4cc-f99fd2c5d89f

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tau_value
import Theorems.Thm_mme_Ctensor_outer_family_double_balanced_extraction
import Theorems.Thm_mme_Ctensor_outer_inner_balanced_weight_sqrt_loss

open MME BigOperators Filter

universe u

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {A H volume : ℕ}
    (stars : CTensorOneHOneFamilyCertificate T A H volume)
    (hA : 0 < A) (hH : 0 < H) (hvolume : 0 < volume)
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let R : ℕ := A ^ 3 * H * m
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization T).kronPow R) ∧
          ((((A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
                (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
              Real.exp
                (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) := by
  obtain ⟨C, hC, hweight⟩ :=
    mme_Ctensor_outer_inner_balanced_weight_sqrt_loss
      A H volume hA hH hvolume tau htau
  refine ⟨C, hC, ?_⟩
  filter_upwards [hweight] with m hm
  dsimp only at hm ⊢
  obtain ⟨k, a, b, c, hrestrict, hk, hvol⟩ :=
    mme_Ctensor_outer_family_double_balanced_extraction
      stars hA hH m
  refine ⟨k, a, b, c, ?_, ?_⟩
  · simpa [mul_assoc] using hrestrict
  · let n : ℕ := A ^ 3
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
    let count : ℝ :=
      (Wouter : ℝ) *
        (((Winner : ℝ) ^ 2 *
          Real.exp
            (-100 * Real.sqrt
              (Real.log (((Winner + 1 : ℕ) : ℝ))))) ^ n)
    let q : ℝ := (((volume ^ (3 * R) : ℕ) : ℝ) ^ tau)
    have hq : 0 ≤ q := by
      dsimp [q]
      positivity
    have hk' : count ≤ (k : ℝ) := by
      simpa [count, Wouter, Winner, n, r, R] using hk
    have hsum :
        (∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau)) =
          (k : ℝ) * q := by
      dsimp [q, R, n, r]
      simp_rw [hvol]
      simp
    rw [hsum]
    have hm' :
        ((((A : ℝ) ^ 3 * (H : ℝ) ^ 2 *
              (((volume ^ 3 : ℕ) : ℝ) ^ tau)) ^ R) *
            Real.exp
              (-C * Real.sqrt (((R + 1 : ℕ) : ℝ))) ≤ count * q) := by
      simpa [count, Wouter, Winner, n, r, R, q] using hm
    simpa [R, n, r, mul_assoc] using
      hm'.trans (mul_le_mul_of_nonneg_right hk' hq)
