-- Prove2me | solution 1 for crouzeix_palencia_of_smoothJordanOuterApproximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:38:41.869427+00:00
-- url     : https://prove2.me/submissions/191a87a5-73c0-4e6c-bae5-c304277bb209

import Definitions.Def_Operator_Crouzeix_SmoothJordanMergelyanAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanOuterApproximation
import Theorems.Thm_convex_numericalRange
import Theorems.Thm_crouzeix_palencia_of_strictNestedSmoothJordanExhaustion
import Theorems.Thm_norm_le_of_mem_numericalRange


set_option autoImplicit false
open Complex Metric Set
open scoped InnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E)
    (houter : HasSmoothJordanOuterApproximation
      (closure (numericalRange A))) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hcompact : IsCompact (closure (numericalRange A)) := by
    have hbounded : Bornology.IsBounded (numericalRange A) :=
      Metric.isBounded_closedBall.subset (fun z hz => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_mem_numericalRange A hz)
    exact hbounded.isCompact_closure
  exact crouzeix_palencia_of_strictNestedSmoothJordanExhaustion A
    (StrictNestedSmoothJordanExhaustion.ofOuterApproximation
      (closure (numericalRange A)) hcompact
        (convex_numericalRange A).closure houter)
