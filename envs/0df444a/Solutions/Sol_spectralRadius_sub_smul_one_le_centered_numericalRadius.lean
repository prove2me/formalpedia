-- Prove2me | solution 1 for spectralRadius_sub_smul_one_le_centered_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:47.486443+00:00
-- url     : https://prove2.me/submissions/b9bbb682-ac16-4d4b-abe7-4c9dcbdffbf2

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_spectralRadius_le_numericalRadius

set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (c : ℂ) :
    spectralRadius ℂ (A - c • (1 : E →L[ℂ] E)) ≤
      ENNReal.ofReal (numericalRadius (A - c • (1 : E →L[ℂ] E))) :=
  spectralRadius_le_numericalRadius
    (A - c • (1 : E →L[ℂ] E))
