-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanion_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:23:16.699577+00:00
-- url     : https://prove2.me/submissions/e4c72725-c5bb-4ff7-87f7-4ef6cfdceb31

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_of_isBounded

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  exact
    tendsto_crouzeixPolynomialScalarCompanion_of_isBounded
      Omega p
        (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hxi
