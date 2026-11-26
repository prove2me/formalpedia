-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_smul_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:10.211809+00:00
-- url     : https://prove2.me/submissions/d1840e68-f4c2-47f0-b8ce-70a6a402d868

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_smul_of_regularized


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (a : ℂ) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {z : ℂ} (hz : z ∈ closure Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega (a • p) z =
      star a * crouzeixPolynomialScalarCompanionClosedExtension Omega p z := by
  apply
    crouzeixPolynomialScalarCompanionClosedExtension_smul_of_regularized
      Omega a p hkernel
  · intro xi hxi
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel hxi
  · exact hz
