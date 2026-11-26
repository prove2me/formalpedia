-- Prove2me | solution 1 for crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:23:15.794954+00:00
-- url     : https://prove2.me/submissions/4dc4cf3f-e2e1-43d1-bd04-119687ebddc1

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_SmoothJordanDomain_isBounded_carrier_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_isBounded

set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (A : E →L[ℂ] E) (Omega : SmoothJordanDomain) (a : ℂ)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1) :
    crouzeixAuxiliaryOperator A Omega
        (crouzeixPolynomialScalarCompanionClosedExtension
          Omega (Polynomial.C a)) =
      crouzeixPolynomialAuxiliaryOperator A Omega (Polynomial.C a) := by
  exact
    crouzeixAuxiliaryOperator_scalarCompanionClosedExtension_C_of_isBounded
      A Omega a (Omega.isBounded_carrier_of_cauchyKernel_eq_one hkernel)
        hkernel
