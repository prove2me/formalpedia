-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_mass_support
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:16:34.664512+00:00
-- url     : https://prove2.me/submissions/952cceaa-133b-427c-89f1-4535108e1a52

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Theorems.Thm_intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
import Theorems.Thm_crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_support

set_option autoImplicit false
open Complex MeasureTheory Polynomial Set
open scoped ComplexConjugate Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hmass : ∀ xi ∈ frontier Omega.carrier,
      (∫ t in (0 : ℝ)..(2 * Real.pi),
        crouzeixBoundaryDoubleLayerDensity Omega xi t) = 1)
    (hsupport : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
          (xi - Omega.boundaryParam t)).re ≤ 0) :
    CrouzeixBoundaryPhaseContractive Omega p := by
  apply
    crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_support
      Omega p
  · intro xi hxi
    exact
      intervalIntegrable_crouzeixBoundaryDoubleLayerDensity_of_integral_eq_one
        Omega xi (hmass xi hxi)
  · exact hmass
  · exact hsupport
