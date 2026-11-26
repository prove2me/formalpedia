-- Prove2me | solution 1 for isUnit_of_forall_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:43.868503+00:00
-- url     : https://prove2.me/submissions/c0ad80fb-02f0-416b-8888-27ba6f8150b4

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution (B : E →L[ℂ] E) {d : ℝ} (hd : 0 < d)
    (hB : ∀ x, d * ‖x‖ ≤ ‖B x‖) (hB' : ∀ x, d * ‖x‖ ≤ ‖(adjoint B) x‖) : IsUnit B := by
  rw [ContinuousLinearMap.isUnit_iff_bijective]
  have hanti : AntilipschitzWith ⟨d⁻¹, inv_nonneg.mpr hd.le⟩ B := by
    refine B.antilipschitz_of_bound fun x => ?_
    calc ‖x‖ = d⁻¹ * (d * ‖x‖) := by field_simp
      _ ≤ d⁻¹ * ‖B x‖ := mul_le_mul_of_nonneg_left (hB x) (inv_nonneg.mpr hd.le)
  refine ⟨hanti.injective, ?_⟩
  have hclosed : IsClosed (Set.range B) := hanti.isClosed_range B.uniformContinuous
  have hdense : (LinearMap.range (B : E →ₗ[ℂ] E)).topologicalClosure = ⊤ := by
    rw [Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal'] at hy
    have h0 : (adjoint B) y = 0 := by
      rw [← inner_self_eq_zero (𝕜 := ℂ), adjoint_inner_left]
      exact hy _ (LinearMap.mem_range_self (B : E →ₗ[ℂ] E) _)
    have h1 : d * ‖y‖ ≤ d * 0 := by
      rw [mul_zero]
      simpa only [h0, norm_zero] using hB' y
    exact norm_le_zero_iff.mp (le_of_mul_le_mul_left h1 hd)
  have hclosed' : IsClosed ((LinearMap.range (B : E →ₗ[ℂ] E) : Submodule ℂ E) : Set E) := hclosed
  have hrange : LinearMap.range (B : E →ₗ[ℂ] E) = ⊤ := by
    rw [← hclosed'.submodule_topologicalClosure_eq]; exact hdense
  exact LinearMap.range_eq_top.mp hrange
