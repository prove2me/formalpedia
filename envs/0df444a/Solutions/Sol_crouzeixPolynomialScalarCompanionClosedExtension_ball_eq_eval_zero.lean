-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_ball_eq_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:28:34.701802+00:00
-- url     : https://prove2.me/submissions/133c2205-8d74-44e9-822f-fe5adc98fa6d

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_crouzeixScalarCauchyKernel_ball_eq_one
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_ball
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_ball_eq_eval_zero
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
import Theorems.Thm_crouzeixPolynomialScalarCompanion_ball_eq_eval_zero


set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball 0 R hR) p z =
      star (Polynomial.eval 0 p) := by
  rw [← Metric.ball_union_sphere] at hz
  rcases hz with hz | hz
  · rw [crouzeixPolynomialScalarCompanionClosedExtension_eq
      (SmoothJordanDomain.ball 0 R hR) p hz,
      crouzeixPolynomialScalarCompanion_ball_eq_eval_zero hR p hz]
  · have hkernel : ∀ w ∈ (SmoothJordanDomain.ball 0 R hR).carrier,
        crouzeixScalarCauchyKernel (SmoothJordanDomain.ball 0 R hR) w = 1 :=
      fun w hw ↦ crouzeixScalarCauchyKernel_ball_eq_one hR hw
    have hreg : ∀ xi ∈ frontier (SmoothJordanDomain.ball 0 R hR).carrier,
        Tendsto
          (crouzeixPolynomialScalarCompanionRegularized
            (SmoothJordanDomain.ball 0 R hR) p xi)
          (nhdsWithin xi (SmoothJordanDomain.ball 0 R hR).carrier)
          (nhds
            (crouzeixPolynomialScalarCompanionRegularized
              (SmoothJordanDomain.ball 0 R hR) p xi xi)) := by
      intro xi hxi
      apply tendsto_crouzeixPolynomialScalarCompanionRegularized_ball hR p
      change xi ∈ frontier (Metric.ball (0 : ℂ) R) at hxi
      rwa [frontier_ball 0 hR.ne'] at hxi
    have hzfrontier : z ∈ frontier
        (SmoothJordanDomain.ball 0 R hR).carrier := by
      change z ∈ frontier (Metric.ball (0 : ℂ) R)
      rwa [frontier_ball 0 hR.ne']
    rw [crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
      (SmoothJordanDomain.ball 0 R hR) p hkernel hreg hzfrontier,
      crouzeixPolynomialScalarCompanionBoundaryValue_ball_eq_eval_zero hR p hz]
