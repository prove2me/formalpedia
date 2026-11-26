-- Prove2me | solution 1 for norm_le_numericalRadius_of_mem_closure_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:55:50.970812+00:00
-- url     : https://prove2.me/submissions/49ac974f-2401-4f74-b240-bde979175488

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_closure_numericalRange_subset_closedBall_numericalRadius
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
theorem _root_.solution
    (A : E →L[ℂ] E) {z : ℂ} (hz : z ∈ closure (numericalRange A)) :
    ‖z‖ ≤ numericalRadius A := by
  have hz' := closure_numericalRange_subset_closedBall_numericalRadius A hz
  simpa only [Metric.mem_closedBall, dist_zero_right] using hz'
