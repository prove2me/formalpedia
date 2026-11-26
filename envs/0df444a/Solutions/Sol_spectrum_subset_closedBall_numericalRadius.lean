-- Prove2me | solution 1 for spectrum_subset_closedBall_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:22:06.700377+00:00
-- url     : https://prove2.me/submissions/f7316762-cf2a-4f02-a86b-36d16818be4d

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_closure_numericalRange_subset_closedBall_numericalRadius
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) :
    spectrum ℂ A ⊆ Metric.closedBall 0 (numericalRadius A) :=
  (spectrum_subset_closure_numericalRange A).trans
    (closure_numericalRange_subset_closedBall_numericalRadius A)
