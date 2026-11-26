-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:35.338062+00:00
-- url     : https://prove2.me/submissions/ff08e384-863b-48ea-9bb3-8624bbab6fd3

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    crouzeixPolynomialScalarCompanionClosedExtension Omega p xi =
      crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi := by
  apply
    crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
      Omega p hkernel
  · intro eta heta
    exact
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
        Omega p hbounded hkernel heta
  · exact hxi
