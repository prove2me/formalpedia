-- Prove2me | solution 1 for spectrum_subset_closure_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:03:33.018625+00:00
-- url     : https://prove2.me/submissions/bb90a1ad-1c02-420a-bf28-0d722b487708

import Mathlib.Algebra.Algebra.Spectrum.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.Normed.Operator.Banach
import Definitions.Def_Operator_NumericalRange_Helpers
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Theorems.Thm_norm_apply_ge_of_forall_unit
import Theorems.Thm_isUnit_of_forall_norm_le
import Theorems.Thm_inner_sub_smul_one_apply_self
import Theorems.Thm_mem_numericalRange
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open scoped InnerProductSpace
open ContinuousLinearMap
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) :
    spectrum ℂ (A : E →L[ℂ] E) ⊆ closure (numericalRange A) := by
  intro l hl
  by_contra hl'
  obtain ⟨d, hd, hfar⟩ : ∃ d > 0, ∀ z ∈ numericalRange A, d ≤ ‖z - l‖ := by
    rw [Metric.mem_closure_iff] at hl'
    push Not at hl'
    obtain ⟨d, hd, h⟩ := hl'
    exact ⟨d, hd, fun z hz => by simpa only [dist_eq_norm, norm_sub_rev] using h z hz⟩
  have hunit : ∀ x : E, ‖x‖ = 1 → d ≤ ‖⟪x, (A - l • 1) x⟫_ℂ‖ := fun x hx => by
    rw [inner_sub_smul_one_apply_self A l hx]
    exact hfar _ ⟨x, hx, rfl⟩
  have hunit' : ∀ x : E, ‖x‖ = 1 → d ≤ ‖⟪x, (adjoint (A - l • 1)) x⟫_ℂ‖ := fun x hx => by
    rw [adjoint_inner_right, ← inner_conj_symm ((A - l • 1) x) x, RCLike.norm_conj]
    exact hunit x hx
  have hU : IsUnit (A - l • 1) :=
    isUnit_of_forall_norm_le (A - l • 1) hd (norm_apply_ge_of_forall_unit _ hunit)
      (norm_apply_ge_of_forall_unit _ hunit')
  apply spectrum.mem_iff.mp hl
  rw [Algebra.algebraMap_eq_smul_one, ← neg_sub]
  exact hU.neg
