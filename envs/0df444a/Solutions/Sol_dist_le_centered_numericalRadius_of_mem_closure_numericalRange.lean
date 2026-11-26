-- Prove2me | solution 1 for dist_le_centered_numericalRadius_of_mem_closure_numericalRange
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:30:54.996787+00:00
-- url     : https://prove2.me/submissions/3e36708c-99d6-4b2d-b1d1-0ed196e58c59

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_closure_numericalRange_subset_closedBall_centered_numericalRadius

set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : z ∈ closure (numericalRange A)) :
    dist z c ≤ numericalRadius (A - c • 1) := by
  exact closure_numericalRange_subset_closedBall_centered_numericalRadius
    A c hz
