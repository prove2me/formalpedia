-- Prove2me | solution 1 for smoothJordanInwardPoint_mem_carrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:45:05.475429+00:00
-- url     : https://prove2.me/submissions/d2f050ce-e33a-4fc8-9469-1f424dc67872

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_crouzeixPolynomialBoundaryPhaseTransform_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionDeriv_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanion_zero
import Theorems.Thm_mem_numericalRange
attribute [local simp] crouzeixPolynomialBoundaryPhaseTransform_zero
attribute [local simp] crouzeixPolynomialScalarCompanionBoundaryValue_zero
attribute [local simp] crouzeixPolynomialScalarCompanionDeriv_zero
attribute [local simp] crouzeixPolynomialScalarCompanionRegularized_zero
attribute [local simp] crouzeixPolynomialScalarCompanion_zero
attribute [local simp] mem_numericalRange



set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) {c xi : ℂ}
    (hc : c ∈ Omega.carrier) (hxi : xi ∈ frontier Omega.carrier)
    {r : ℝ} (hr : r ∈ Ioc (0 : ℝ) 1) :
    smoothJordanInwardPoint c xi r ∈ Omega.carrier := by
  have hcint : c ∈ interior Omega.carrier := by
    rwa [Omega.isOpen_carrier.interior_eq]
  have hcombo :=
    Omega.strictConvex_carrier.convex.combo_closure_interior_mem_interior
      (frontier_subset_closure hxi) hcint
      (sub_nonneg.mpr hr.2) hr.1 (by ring)
  exact interior_subset (by
    simpa only [smoothJordanInwardPoint] using hcombo)
