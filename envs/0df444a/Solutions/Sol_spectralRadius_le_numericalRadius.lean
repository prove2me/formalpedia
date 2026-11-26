-- Prove2me | solution 1 for spectralRadius_le_numericalRadius
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:59:59.466729+00:00
-- url     : https://prove2.me/submissions/8b1fa704-dc76-4ea0-a90c-79b3e70c91c5

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
theorem _root_.solution (A : E →L[ℂ] E) :
    spectralRadius ℂ A ≤ ENNReal.ofReal (numericalRadius A) := by
  unfold spectralRadius
  refine iSup₂_le fun z hz => ?_
  rw [← enorm_eq_nnnorm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    (norm_le_numericalRadius_of_mem_spectrum A hz)
