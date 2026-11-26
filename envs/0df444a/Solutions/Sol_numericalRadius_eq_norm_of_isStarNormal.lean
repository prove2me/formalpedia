-- Prove2me | solution 1 for numericalRadius_eq_norm_of_isStarNormal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:23.29132+00:00
-- url     : https://prove2.me/submissions/019e06f0-2b79-42ce-b47b-be246876096a

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_le_norm
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRange_scalar
import Theorems.Thm_numericalRange_zero
import Theorems.Thm_spectralRadius_toReal_le_numericalRadius
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_neg
attribute [local simp] numericalRange_scalar
attribute [local simp] numericalRange_zero



set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) [IsStarNormal A] :
    numericalRadius A = ‖A‖ := by
  by_cases hE : Nontrivial E
  · let _ : Nontrivial E := hE
    apply le_antisymm (numericalRadius_le_norm A)
    have h := spectralRadius_toReal_le_numericalRadius A
    rw [IsStarNormal.spectralRadius_eq_nnnorm A] at h
    simpa using h
  · let _ : Subsingleton E := not_nontrivial_iff_subsingleton.mp hE
    have hA : A = 0 := Subsingleton.elim _ _
    subst A
    simp only [numericalRadius_zero, norm_zero]
