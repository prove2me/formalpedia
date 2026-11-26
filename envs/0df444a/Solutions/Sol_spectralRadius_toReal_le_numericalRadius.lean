-- Prove2me | solution 1 for spectralRadius_toReal_le_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:00:46.784974+00:00
-- url     : https://prove2.me/submissions/5b1316b7-ad33-4fd4-817f-881f0d629aa5

import Mathlib.Analysis.Normed.Algebra.Spectrum
import Definitions.Def_Operator_NumericalRange_Affine
import Definitions.Def_Operator_NumericalRange_Radius
import Definitions.Def_Operator_SpectralSet_SpectrumInNR
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Theorems.Thm_spectralRadius_le_numericalRadius
import Theorems.Thm_numericalRadius_nonneg


set_option autoImplicit false
open Set
open scoped ENNReal InnerProductSpace NNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable [CompleteSpace E]
theorem _root_.solution (A : E →L[ℂ] E) :
    (spectralRadius ℂ A).toReal ≤ numericalRadius A := by
  calc
    (spectralRadius ℂ A).toReal ≤
        (ENNReal.ofReal (numericalRadius A)).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (spectralRadius_le_numericalRadius A)
    _ = numericalRadius A :=
      ENNReal.toReal_ofReal (numericalRadius_nonneg A)
