-- Prove2me | solution 1 for re_inner_smul_resolvent_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:30:45.103873+00:00
-- url     : https://prove2.me/submissions/fd9c960b-5aec-4ee3-b670-f755400ae464

import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.InnerProductSpace.Positive
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_Crouzeix_DoubleLayer
import Theorems.Thm_eq_smul_resolvent_apply_sub_apply
import Theorems.Thm_inner_inv_norm_smul_apply
import Theorems.Thm_norm_inv_norm_smul


set_option autoImplicit false
open Complex
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (A : E →L[ℂ] E) {σ ν : ℂ}
    (hW : ∀ w ∈ numericalRange A, ((starRingEnd ℂ) ν * (w - σ)).re ≤ 0) (x : E) :
    0 ≤ (⟪x, (ν • resolvent A σ) x⟫_ℂ).re := by
  by_cases hσ : σ ∈ resolventSet ℂ A
  · rw [smul_apply, inner_smul_right]
    set y := resolvent A σ x with hy
    have hx : x = σ • y - A y := eq_smul_resolvent_apply_sub_apply A hσ x
    by_cases hy0 : y = 0
    · rw [hy0, inner_zero_right, mul_zero, Complex.zero_re]
    · set a := ⟪y, A y⟫_ℂ / (‖y‖ : ℂ) ^ 2 with ha_def
      have hmem : a ∈ numericalRange A := by
        refine ⟨((‖y‖ : ℂ)⁻¹) • y, norm_inv_norm_smul hy0, ?_⟩
        exact inner_inv_norm_smul_apply A hy0
      have hne : (‖y‖ : ℂ) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy0))
      have ha : ⟪y, A y⟫_ℂ = (‖y‖ : ℂ) ^ 2 * a := by
        rw [ha_def, mul_div_cancel₀ _ hne]
      have hyy : ⟪y, y⟫_ℂ = (‖y‖ : ℂ) ^ 2 := inner_self_eq_norm_sq_to_K y
      have hinner : ⟪x, y⟫_ℂ = (‖y‖ : ℂ) ^ 2 * (starRingEnd ℂ) (σ - a) := by
        rw [hx, inner_sub_left, inner_smul_left, ← inner_conj_symm (A y) y, hyy, ha, map_sub,
          map_mul, map_pow, Complex.conj_ofReal]
        ring
      have hre : (ν * ⟪x, y⟫_ℂ).re = ‖y‖ ^ 2 * ((starRingEnd ℂ) ν * (σ - a)).re := by
        rw [hinner]
        have h1 : ν * ((‖y‖ : ℂ) ^ 2 * (starRingEnd ℂ) (σ - a)) =
            ((‖y‖ ^ 2 : ℝ) : ℂ) * (starRingEnd ℂ) ((starRingEnd ℂ) ν * (σ - a)) := by
          rw [map_mul, Complex.conj_conj, Complex.ofReal_pow]
          ring
        rw [h1, Complex.re_ofReal_mul, Complex.conj_re]
      rw [hre, ← neg_sub a σ, mul_neg, Complex.neg_re]
      exact mul_nonneg (sq_nonneg _) (neg_nonneg.mpr (hW a hmem))
  · have hσ' : σ ∈ spectrum ℂ A := hσ
    rw [spectrum.resolvent_zero_of_mem_spectrum hσ', smul_zero, zero_apply, inner_zero_right,
      Complex.zero_re]
