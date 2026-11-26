-- Prove2me | solution 1 for spectrum_subset_closedBall_centered_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:56:19.395205+00:00
-- url     : https://prove2.me/submissions/e7aefdae-264d-40dc-9843-6b23b35354a4

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_closure_numericalRange_subset_closedBall_centered_numericalRadius
import Theorems.Thm_spectrum_subset_closure_numericalRange


set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    spectrum ℂ A ⊆ Metric.closedBall c (numericalRadius (A - c • 1)) :=
  (spectrum_subset_closure_numericalRange A).trans
    (closure_numericalRange_subset_closedBall_centered_numericalRadius A c)
