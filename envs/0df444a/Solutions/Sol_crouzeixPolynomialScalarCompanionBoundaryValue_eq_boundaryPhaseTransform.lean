-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionBoundaryValue_eq_boundaryPhaseTransform
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:54.076301+00:00
-- url     : https://prove2.me/submissions/1be587fd-20eb-4321-8b4d-9ac5270a3279

import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionDecay
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljBound
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform

set_option autoImplicit false
open Complex Set
open scoped Interval Real
theorem _root_.solution
    (Omega : SmoothJordanDomain) (p : Polynomial ℂ) (xi : ℂ) :
    crouzeixPolynomialScalarCompanionBoundaryValue Omega p xi =
      star (Polynomial.eval xi p) +
        crouzeixPolynomialBoundaryPhaseTransform Omega xi
          (p /ₘ (Polynomial.X - Polynomial.C xi)) := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [
    crouzeixPolynomialScalarCompanionRegularized_self_eq_boundaryPhaseTransform]
