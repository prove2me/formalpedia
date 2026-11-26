-- Prove2me | solution 1 for tendsto_crouzeixPolynomialScalarCompanion_of_isBounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:18:46.568301+00:00
-- url     : https://prove2.me/submissions/4c03849f-f132-4924-a847-19481f485120

import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_Operator_Crouzeix_ScalarCompanionRadial
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanion_of_regularized


set_option autoImplicit false
open Complex Filter MeasureTheory Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ)
    (hbounded : Bornology.IsBounded Omega.carrier)
    (hkernel : ∀ z ∈ Omega.carrier,
      crouzeixScalarCauchyKernel Omega z = 1)
    {xi : ℂ} (hxi : xi ∈ frontier Omega.carrier) :
    Filter.Tendsto (crouzeixPolynomialScalarCompanion Omega p)
      (nhdsWithin xi Omega.carrier)
      (nhds (crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi)) := by
  apply tendsto_crouzeixPolynomialScalarCompanion_of_regularized
    Omega p hkernel xi
  exact
    tendsto_crouzeixPolynomialScalarCompanionRegularized_of_isBounded
      Omega p hbounded hkernel hxi
