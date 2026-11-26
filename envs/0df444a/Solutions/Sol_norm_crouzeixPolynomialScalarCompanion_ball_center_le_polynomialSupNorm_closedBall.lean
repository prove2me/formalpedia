-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_ball_center_le_polynomialSupNorm_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:51:27.89899+00:00
-- url     : https://prove2.me/submissions/df7c1f8f-5e89-4954-8a05-7349a8dbf8de

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Theorems.Thm_crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center
import Theorems.Thm_bddAbove_norm_eval_image_of_isCompact
import Theorems.Thm_norm_eval_le_polynomialSupNorm


set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
theorem _root_.solution
    (c : ℂ) {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball c R) :
    ‖crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball c R hR) p z‖ ≤
      polynomialSupNorm p (Metric.closedBall c R) := by
  rw [crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center c hR p hz,
    norm_star]
  exact norm_eval_le_polynomialSupNorm p
    (bddAbove_norm_eval_image_of_isCompact p (isCompact_closedBall c R))
    (Metric.mem_closedBall_self hR.le)
