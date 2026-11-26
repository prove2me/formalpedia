-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:14:18.722206+00:00
-- url     : https://prove2.me/submissions/6dbcf475-f324-40cd-9c65-a9467a380357

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPhaseInduction
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanionBoundaryValue_le_of_boundaryDoubleLayerDensity
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform


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
    (hpos : ∀ xi ∈ frontier Omega.carrier,
      ∀ t ∈ Ioc (0 : ℝ) (2 * Real.pi),
        0 ≤ crouzeixBoundaryDoubleLayerDensity Omega xi t) :
    CrouzeixBoundaryPhaseContractive Omega p := by
  intro xi hxi
  rw [←
    crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform]
  exact
    norm_crouzeixPolynomialScalarCompanionBoundaryValue_le_of_boundaryDoubleLayerDensity
      Omega p hxi (hrho xi hxi) (hmass xi hxi) (hpos xi hxi)
