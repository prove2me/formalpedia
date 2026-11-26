-- Prove2me | solution 1 for numericalRadius_eq_one_of_mem_unitary
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T16:02:00.99939+00:00
-- url     : https://prove2.me/submissions/f731e891-455d-4f93-be29-b034471ef3af

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
    [Nontrivial E] (U : E →L[ℂ] E)
    (hU : U ∈ unitary (E →L[ℂ] E)) :
    numericalRadius U = 1 := by
  let _ : IsStarNormal U := isStarNormal_of_mem_unitary hU
  exact (numericalRadius_eq_norm_of_isStarNormal U).trans
    (CStarRing.norm_of_mem_unitary hU)
