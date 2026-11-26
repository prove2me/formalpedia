-- Prove2me | solution 1 for isUnit_smul_one_sub_of_centered_numericalRadius_lt_dist
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:31:12.802693+00:00
-- url     : https://prove2.me/submissions/951fe65a-6546-46b2-b491-0eaae526158c

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_isUnit_smul_one_sub_of_numericalRadius_lt_norm
import Theorems.Thm_mem_numericalRange
import Theorems.Thm_numericalRadiusSeminorm_apply
import Theorems.Thm_numericalRadius_neg
import Theorems.Thm_numericalRange_scalar
import Theorems.Thm_numericalRange_zero
attribute [local simp] mem_numericalRange
attribute [local simp] numericalRadiusSeminorm_apply
attribute [local simp] numericalRadius_neg
attribute [local simp] numericalRange_scalar
attribute [local simp] numericalRange_zero



set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : numericalRadius (A - c • 1) < dist z c) :
    IsUnit (z • (1 : E →L[ℂ] E) - A) := by
  have hz' : numericalRadius (A - c • 1) < ‖z - c‖ := by
    simpa only [dist_eq_norm] using hz
  have hu := isUnit_smul_one_sub_of_numericalRadius_lt_norm
    (A - c • (1 : E →L[ℂ] E)) hz'
  have hop :
      (z - c) • (1 : E →L[ℂ] E) - (A - c • 1) = z • 1 - A := by
    module
  rw [hop] at hu
  exact hu
