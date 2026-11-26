-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_add_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:17:40.992424+00:00
-- url     : https://prove2.me/submissions/cc1e2386-4f97-4391-9b22-2e10d8774ba0

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_add_of_regularized


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p q : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (p + q) z =
      crouzeixPolynomialScalarCompanionClosedExtension Omega p z +
        crouzeixPolynomialScalarCompanionClosedExtension Omega q z := by
  apply
    crouzeixPolynomialScalarCompanionClosedExtension_add_of_regularized
      Omega p q hkernel
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel hxi
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega q hbounded hkernel hxi
  · exact hz
