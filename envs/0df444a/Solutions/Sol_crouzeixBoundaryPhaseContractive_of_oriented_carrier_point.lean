-- Prove2me | solution 1 for crouzeixBoundaryPhaseContractive_of_oriented_carrier_point
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:26.334942+00:00
-- url     : https://prove2.me/submissions/15be63d2-871d-448a-b1d9-b2373db154c8

import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasure
import Definitions.Def_Operator_Crouzeix_SmoothJordanSupport
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Definitions.Def_Operator_Crouzeix_ScalarCompanionBoundaryMeasureMass
import Theorems.Thm_integral_crouzeixBoundaryDoubleLayerDensity_eq_one_of_oriented_carrier_point
import Theorems.Thm_SmoothJordanDomain_closure_support_and_carrier_strict_of_support_at_mem_carrier
import Theorems.Thm_crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_mass_support


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (c : ℂ) (hc : c ∈ Omega.carrier)
    (hcside : ∀ t : ℝ,
      ((starRingEnd ℂ) (-I * deriv Omega.boundaryParam t) *
        (c - Omega.boundaryParam t)).re ≤ 0)
    (p : Polynomial ℂ) :
    CrouzeixBoundaryPhaseContractive Omega p := by
  apply
    crouzeixBoundaryPhaseContractive_of_boundaryDoubleLayerDensity_mass_support
      Omega p
  · intro xi hxi
    exact
      integral_crouzeixBoundaryDoubleLayerDensity_eq_one_of_oriented_carrier_point
        Omega c hc hcside xi hxi
  · intro xi hxi t _
    exact
      (Omega.closure_support_and_carrier_strict_of_support_at_mem_carrier
        c hc t (hcside t)).1 xi (frontier_subset_closure hxi)
