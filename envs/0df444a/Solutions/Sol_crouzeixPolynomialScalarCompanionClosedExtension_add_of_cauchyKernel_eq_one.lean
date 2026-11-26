-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_add_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:23:43.935547+00:00
-- url     : https://prove2.me/submissions/1bb614de-1858-41db-8e85-0481b977a06c

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (p + q) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        crouzeixPolynomialScalarCompanionClosedExtension Omega q z := by
  exact
    crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded
      Omega p q (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hz
