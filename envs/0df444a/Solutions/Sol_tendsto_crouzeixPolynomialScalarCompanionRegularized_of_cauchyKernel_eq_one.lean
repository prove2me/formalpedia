-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:34.832858+00:00
-- url     : https://prove2.me/submissions/ae795d1d-9e22-4be6-b6f5-dc7b75583c4e

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto
      (crouzeixPolynomialScalarCompanionRegularized Omega p xi)
      (nhdsWithin xi Omega.carrier)
      (nhds
        (crouzeixPolynomialScalarCompanionRegularized Omega p xi xi)) := by
  exact
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
      Omega p
        (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hxi
