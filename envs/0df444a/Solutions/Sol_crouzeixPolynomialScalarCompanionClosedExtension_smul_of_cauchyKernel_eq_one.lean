-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_smul_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:08.859606+00:00
-- url     : https://prove2.me/submissions/1db62eea-1d7c-4bd3-bacc-d347df90031f

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z := by
  exact
    crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded
      Omega a p (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hz
