-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_le_of_boundary_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:23:45.92483+00:00
-- url     : https://prove2.me/submissions/01b31211-1ddf-467f-a4ec-085a739c6d90

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_le_of_isBounded_boundary

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {C : ℝ}
    (hC : ∀ xi ∈ frontier Omega.carrier,
      ‖crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi‖ ≤ C)
    {z : ℂ} (hz : z ∈ Omega.carrier) :
    ‖crouzeixPolynomialScalarCompanion Omega p z‖ ≤ C := by
  exact
    norm_crouzeixPolynomialScalarCompanion_le_of_isBounded_boundary
      Omega p (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hC hz
