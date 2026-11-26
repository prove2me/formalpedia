-- Prove2me | solution 1 for numericalRadius_eq_norm_of_isSelfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:01:59.494671+00:00
-- url     : https://prove2.me/submissions/b72c7f00-99ca-4113-96b2-2595c206206c

import Mathlib.Analysis.CStarAlgebra.Spectrum
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Definitions.Def_Operator_NumericalRange_RadiusSpectrum
import Definitions.Def_Operator_NumericalRange_RadiusNormal
import Theorems.Thm_numericalRadius_eq_norm_of_isStarNormal

set_option autoImplicit false
open scoped InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (hA : IsSelfAdjoint A) :
    numericalRadius A = ‖A‖ := by
  let _ : IsStarNormal A := hA.isStarNormal
  exact numericalRadius_eq_norm_of_isStarNormal A
