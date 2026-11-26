-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanionClosedExtension_ball_center_eq_eval_center
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:53:46.384789+00:00
-- url     : https://prove2.me/submissions/709e27ef-a3c9-45e3-aa65-c440ca591008

import Definitions.Def_Operator_Crouzeix_PalenciaSupport
import Definitions.Def_Operator_Crouzeix_ProductBase
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemelj
import Definitions.Def_Operator_Crouzeix_ScalarCompanionPlemeljCircle
import Theorems.Thm_crouzeixScalarCauchyKernel_ball_center_eq_one
import Theorems.Thm_tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
import Theorems.Thm_crouzeixPolynomialScalarCompanionBoundaryValue_ball_center_eq_eval_center
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq
import Theorems.Thm_crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
import Theorems.Thm_crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center


set_option autoImplicit false
open Complex ComplexConjugate Filter Polynomial Set
open scoped Interval Real
theorem _root_.solution
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.closedBall c R) :
    crouzeixPolynomialScalarCompanionClosedExtension
        (SmoothJordanDomain.ball c R hR) p z =
      star (Polynomial.eval c p) := by
  rw [← Metric.ball_union_sphere] at hz
  rcases hz with hz | hz
  · rw [crouzeixPolynomialScalarCompanionClosedExtension_eq
      (SmoothJordanDomain.ball c R hR) p hz,
      crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center c hR p hz]
  · have hkernel : ∀ w ∈ (SmoothJordanDomain.ball c R hR).carrier,
        crouzeixScalarCauchyKernel (SmoothJordanDomain.ball c R hR) w = 1 :=
      fun w hw ↦ crouzeixScalarCauchyKernel_ball_center_eq_one c hR hw
    have hreg : ∀ xi ∈ frontier (SmoothJordanDomain.ball c R hR).carrier,
        Tendsto
          (crouzeixPolynomialScalarCompanionRegularized
            (SmoothJordanDomain.ball c R hR) p xi)
          (nhdsWithin xi (SmoothJordanDomain.ball c R hR).carrier)
          (nhds
            (crouzeixPolynomialScalarCompanionRegularized
              (SmoothJordanDomain.ball c R hR) p xi xi)) := by
      intro xi hxi
      apply tendsto_crouzeixPolynomialScalarCompanionRegularized_ball_center
        c hR p
      change xi ∈ frontier (Metric.ball c R) at hxi
      rwa [frontier_ball c hR.ne'] at hxi
    have hzfrontier : z ∈ frontier
        (SmoothJordanDomain.ball c R hR).carrier := by
      change z ∈ frontier (Metric.ball c R)
      rwa [frontier_ball c hR.ne']
    rw [crouzeixPolynomialScalarCompanionClosedExtension_eq_boundaryValue_of_regularized
      (SmoothJordanDomain.ball c R hR) p hkernel hreg hzfrontier,
      crouzeixPolynomialScalarCompanionBoundaryValue_ball_center_eq_eval_center
        c hR p hz]
