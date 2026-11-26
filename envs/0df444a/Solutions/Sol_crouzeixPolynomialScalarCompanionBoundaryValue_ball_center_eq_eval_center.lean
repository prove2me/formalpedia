-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionBoundaryValue_ball_center_eq_eval_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:40.153178+00:00
-- url     : https://prove2.me/submissions/67f86c3d-c430-47f5-9997-e30f02b21254

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq

set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
theorem _root_.solution
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {xi : ℂ}
    (hxi : xi ∈ Metric.sphere c R) :
    crouzeixPolynomialScalarCompanionBoundaryValue
        (SmoothJordanDomain.ball c R hR) p xi =
      star (Polynomial.eval c p) := by
  unfold crouzeixPolynomialScalarCompanionBoundaryValue
  rw [crouzeixPolynomialScalarCompanionRegularized_ball_center_boundary_eq
    c hR p hxi]
  ring
