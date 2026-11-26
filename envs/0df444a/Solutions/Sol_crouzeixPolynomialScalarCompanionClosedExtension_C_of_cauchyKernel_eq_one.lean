-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:22:12.201128+00:00
-- url     : https://prove2.me/submissions/2d774b1c-ebec-4c59-b88c-4490b8465532

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension
        Omega (Polynomial.C a) z = star a := by
  exact
    crouzeixPolynomialScalarCompanionClosedExtension_C_of_isBounded
      Omega a (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel hz
