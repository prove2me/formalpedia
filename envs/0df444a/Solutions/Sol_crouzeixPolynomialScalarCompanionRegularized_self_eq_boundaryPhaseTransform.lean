-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:11:44.303391+00:00
-- url     : https://prove2.me/submissions/1be0f2ec-ec86-4775-9c6f-444d88ac05ed

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionRegularized Omega p xi xi =
      crouzeixPolynomialBoundaryPhaseTransform Omega xi
        (p /ₘ (Polynomial.X - Polynomial.C xi)) := by
  unfold crouzeixPolynomialBoundaryPhaseTransform
  exact
    crouzeixPolynomialScalarCompanionRegularized_self_eq_divByMonic
      Omega p xi
