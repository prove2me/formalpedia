-- Prove2me | solution 1 for norm_apply_ge_of_forall_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:42.75695+00:00
-- url     : https://prove2.me/submissions/425c2463-4fa7-432f-b19f-33497e0dc882

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_norm_inv_norm_smul
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution (B : E →L[ℂ] E) {d : ℝ}
    (h : ∀ x : E, ‖x‖ = 1 → d ≤ ‖⟪x, B x⟫_ℂ‖) (x : E) : d * ‖x‖ ≤ ‖B x‖ := by
  by_cases hx : x = 0
  · subst x
    simp only [norm_zero, mul_zero, map_zero, le_refl]
  · let y : E := ((‖x‖ : ℂ)⁻¹) • x
    have hy : ‖y‖ = 1 := norm_inv_norm_smul hx
    have hBy : d ≤ ‖B y‖ := calc
      d ≤ ‖⟪y, B y⟫_ℂ‖ := h y hy
      _ ≤ ‖y‖ * ‖B y‖ := norm_inner_le_norm y (B y)
      _ = ‖B y‖ := by rw [hy, one_mul]
    have hscaled : d ≤ ‖x‖⁻¹ * ‖B x‖ := by
      dsimp only [y] at hBy
      simpa only [map_smul, norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg x)] using hBy
    rw [← div_eq_inv_mul] at hscaled
    exact (le_div_iff₀ (norm_pos_iff.mpr hx)).mp hscaled
