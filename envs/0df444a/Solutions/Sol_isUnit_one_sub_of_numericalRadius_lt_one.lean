-- Prove2me | solution 1 for isUnit_one_sub_of_numericalRadius_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:31:13.460624+00:00
-- url     : https://prove2.me/submissions/16bb543f-980b-4003-8464-eaba76665d9d

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
    (A : E →L[ℂ] E) (hA : numericalRadius A < 1) :
    IsUnit (1 - A) := by
  have hA' : numericalRadius A < ‖(1 : ℂ)‖ := by simpa using hA
  simpa only [one_smul] using
    (isUnit_smul_one_sub_of_numericalRadius_lt_norm A hA')
