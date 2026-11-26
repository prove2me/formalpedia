-- Prove2me | solution 1 for norm_le_centered_numericalRadius_of_mem_spectrum_sub_smul_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:30:57.862442+00:00
-- url     : https://prove2.me/submissions/436f40f2-24e2-4cd3-b095-70550978d905

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_norm_le_numericalRadius_of_mem_spectrum

set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (A - c • (1 : E →L[ℂ] E))) :
    ‖z‖ ≤ numericalRadius (A - c • (1 : E →L[ℂ] E)) :=
  norm_le_numericalRadius_of_mem_spectrum
    (A - c • (1 : E →L[ℂ] E)) hz
