-- Prove2me | solution 1 for crouzeix_palencia_of_smoothJordanOuterApproximation_unitBallPolytope_case
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:36:40.549822+00:00
-- url     : https://prove2.me/submissions/9e7ba8eb-6a2f-4e4f-a732-2e0667e92f14

import Definitions.Def_Operator_Crouzeix_SmoothJordanAffine
import Definitions.Def_Operator_Crouzeix_SmoothJordanPolytopeReduction
import Definitions.Def_Operator_Crouzeix_SmoothJordanSimilarity
import Theorems.Thm_hasSmoothJordanOuterApproximationForPolytopes_of_unitBall_case
import Theorems.Thm_crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case


set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E] [Nontrivial E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (hunit : HasSmoothJordanOuterApproximationForUnitBallPolytopes) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  apply crouzeix_palencia_of_smoothJordanOuterApproximation_polytope_case A
  exact hasSmoothJordanOuterApproximationForPolytopes_of_unitBall_case hunit
