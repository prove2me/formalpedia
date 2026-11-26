-- Prove2me | solution 1 for numericalRange_unitary_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:08:36.789334+00:00
-- url     : https://prove2.me/submissions/f07a7bf4-5b40-420a-9e17-0192366bec86

import Definitions.Def_Operator_NumericalRange_Adjoint
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_NumericalRange_RadiusAdjoint
import Theorems.Thm_numericalRadius_adjoint
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_neg
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_neg


attribute [local simp] numericalRadius_adjoint

set_option autoImplicit false
open Complex
open ContinuousLinearMap
open scoped InnerProductSpace InnerProduct
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution (A U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRange (U† * A * U) = numericalRange A := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨U x, (norm_map_of_mem_unitary hU x).trans hx, ?_⟩
    simp only [mul_apply_eq_comp]
    rw [adjoint_inner_right]
  · rintro ⟨x, hx, rfl⟩
    have hUadj : U† ∈ unitary (E →L[ℂ] E) := Unitary.star_mem hU
    refine ⟨(U†) x, (norm_map_of_mem_unitary hUadj x).trans hx, ?_⟩
    have hcancel (v : E) : U ((U†) v) = v := by
      change U ((star U) v) = v
      have h := congrArg (fun T : E →L[ℂ] E => T v)
        (Unitary.mul_star_self_of_mem hU)
      simpa only [mul_apply_eq_comp, one_apply_eq_self] using h
    simp only [mul_apply_eq_comp, hcancel]
    exact inner_map_map_of_mem_unitary hUadj x (A x)
