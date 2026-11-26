-- Prove2me | solution 1 for isUnit_smul_one_sub_of_numericalRadius_lt_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:25:55.029651+00:00
-- url     : https://prove2.me/submissions/8d04662e-44b7-4c47-9514-5f9032132952

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_norm_le_numericalRadius_of_mem_spectrum
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
    (A : E →L[ℂ] E) {z : ℂ} (hz : numericalRadius A < ‖z‖) :
    IsUnit (z • (1 : E →L[ℂ] E) - A) := by
  have hnot : z ∉ spectrum ℂ A := by
    intro hzs
    exact hz.not_ge (norm_le_numericalRadius_of_mem_spectrum A hzs)
  simpa only [Algebra.algebraMap_eq_smul_one] using
    (spectrum.notMem_iff.mp hnot)
