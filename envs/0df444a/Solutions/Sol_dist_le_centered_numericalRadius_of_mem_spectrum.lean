-- Prove2me | solution 1 for dist_le_centered_numericalRadius_of_mem_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:31:09.398353+00:00
-- url     : https://prove2.me/submissions/957ed0df-0e84-49d0-ae40-4a0788016a0e

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_spectrum_subset_closedBall_centered_numericalRadius

set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ} (hz : z ∈ spectrum ℂ A) :
    dist z c ≤ numericalRadius (A - c • 1) :=
  spectrum_subset_closedBall_centered_numericalRadius A c hz
