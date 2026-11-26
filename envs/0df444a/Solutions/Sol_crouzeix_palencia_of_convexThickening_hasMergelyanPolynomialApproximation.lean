-- Prove2me | solution 1 for crouzeix_palencia_of_convexThickening_hasMergelyanPolynomialApproximation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:32:08.311265+00:00
-- url     : https://prove2.me/submissions/2250b45c-514c-4994-a374-f07182fd8e32

import Definitions.Def_Operator_Crouzeix_ResolventContourHomotopy
import Definitions.Def_Operator_Crouzeix_PalenciaSmoothApproximation
import Definitions.Def_Operator_Crouzeix_PolynomialCauchyFromResolventMass
import Definitions.Def_Operator_Crouzeix_ResolventCauchyKernel
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadialAssembly
import Definitions.Def_Operator_Crouzeix_SmoothJordanExhaustion
import Theorems.Thm_crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_hasMergelyanPolynomialApproximation
import Theorems.Thm_norm_le_of_mem_numericalRange


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped InnerProductSpace Interval Real
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]
theorem _root_.solution
    (A : E →L[ℂ] E) (Omega : ℕ → SmoothJordanDomain)
    (hcarrier : ∀ n, (Omega n).carrier =
      convexThickeningApprox (closure (numericalRange A)) n)
    (hmergelyan : ∀ n,
      (Omega n).HasMergelyanPolynomialApproximation) :
    IsKPolynomialSpectralSet A (1 + Real.sqrt 2)
      (closure (numericalRange A)) := by
  have hcompact : IsCompact (closure (numericalRange A)) := by
    have hbounded : Bornology.IsBounded (numericalRange A) :=
      Metric.isBounded_closedBall.subset (fun z hz ↦ by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_le_of_mem_numericalRange A hz)
    exact hbounded.isCompact_closure
  let exhaustion :=
    StrictNestedSmoothJordanExhaustion.ofConvexThickening
      (closure (numericalRange A)) hcompact Omega hcarrier
  apply
    crouzeix_palencia_of_strictNestedSmoothJordanExhaustion_canonicalOrientation_hasMergelyanPolynomialApproximation
      A exhaustion
  intro n
  change (Omega n).HasMergelyanPolynomialApproximation
  exact hmergelyan n
