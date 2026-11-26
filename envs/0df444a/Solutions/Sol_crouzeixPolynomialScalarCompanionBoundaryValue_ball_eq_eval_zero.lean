-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionBoundaryValue_ball_eq_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:55.941095+00:00
-- url     : https://prove2.me/submissions/5a0bce38-df1e-45dd-8764-8919191e7440

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq

set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanionBoundaryValue
        (SmoothJordanDomain.ball 0 R hR) p xi =
      star (Polynomial.eval 0 p) := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_ball_boundary_eq hR p hxi]
  ring
