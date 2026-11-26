-- Prove2me | solution 1 for spectrum_sub_smul_one_subset_closedBall_centered_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:30:57.124813+00:00
-- url     : https://prove2.me/submissions/96ea3f48-2854-4895-aef1-d0c44a28684a

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_spectrum_subset_closedBall_numericalRadius

set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    spectrum ℂ (A - c • (1 : E →L[ℂ] E)) ⊆
      Metric.closedBall 0
        (numericalRadius (A - c • (1 : E →L[ℂ] E))) :=
  spectrum_subset_closedBall_numericalRadius
    (A - c • (1 : E →L[ℂ] E))
