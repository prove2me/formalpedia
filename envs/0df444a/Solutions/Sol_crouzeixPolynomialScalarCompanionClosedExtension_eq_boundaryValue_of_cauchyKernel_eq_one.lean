-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_cauchyKernel_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:23:22.516802+00:00
-- url     : https://prove2.me/submissions/abf7509f-1b0f-424b-8fcb-12f489317a2e

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
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
      tendsto_crouzeixPolynomialScalarCompanionRegularized_of_cauchyKernel_eq_one
        Omega p hkernel heta
  · exact hxi
