-- Prove2me | solution 1 for spectralRadius_sub_smul_one_toReal_le_centered_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:23.854056+00:00
-- url     : https://prove2.me/submissions/2c80e5e9-e11b-4fe9-b4f2-1d566738bec6

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_spectralRadius_toReal_le_numericalRadius

set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    (spectralRadius ℂ (A - c • (1 : E →L[ℂ] E))).toReal ≤
      numericalRadius (A - c • (1 : E →L[ℂ] E)) :=
  spectralRadius_toReal_le_numericalRadius
    (A - c • (1 : E →L[ℂ] E))
