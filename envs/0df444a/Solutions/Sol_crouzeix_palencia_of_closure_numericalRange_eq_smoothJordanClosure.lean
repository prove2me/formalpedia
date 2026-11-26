-- Prove2me | solution 1 for crouzeix_palencia_of_closure_numericalRange_eq_smoothJordanClosure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:35:42.667222+00:00
-- url     : https://prove2.me/submissions/3fe3c8d9-6abe-4f5a-a091-394e0b1f1d72

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanCompact
import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
import Definitions.Def_Operator_Crouzeix_SmoothJordanInflation
import Theorems.Thm_SmoothJordanDomain_hasSmoothJordanOuterApproximation_closure
import Theorems.Thm_crouzeix_palencia_of_smoothJordanOuterApproximation


set_option autoImplicit false
open Complex Metric Set
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain)
    (hW : closure (numericalRange A) = closure Omega.carrier) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_smoothJordanOuterApproximation A
  rw [hW]
  exact Omega.hasSmoothJordanOuterApproximation_closure
