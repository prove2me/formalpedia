-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:15:22.941589+00:00
-- url     : https://prove2.me/submissions/129891bc-5448-4de5-8099-f30dd477d32c

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Theorems.Thm_crouzeixBoundaryDoubleLayerDensity_nonneg_of_support
import Theorems.Thm_crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity

set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hrho : ∀ xi ∈ frontier Omega.carrier,
      IntervalIntegrable (crouzeixBoundaryDoubleLayerDensity Omega xi)
        volume 0 (2 * Real.pi))
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hsupport : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (xi - Omega.boundaryParam t)).re ≤ 0) :
    CrouzeixBoundaryPhaseContractive Omega p := by
  apply crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
    Omega p hrho hmass
  intro xi hxi t ht
  exact crouzeixBoundaryDoubleLayerDensity_nonneg_of_support
    Omega xi t (hsupport xi hxi t ht)
