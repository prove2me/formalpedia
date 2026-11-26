-- Prove2me | solution 1 for norm_crouzeixPolynomialScalarCompanion_ball_le_polynomialSupNorm_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:28:25.896531+00:00
-- url     : https://prove2.me/submissions/d68e5bce-5672-4629-877a-6c1bb40d67b0

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Theorems.Thm_norm_crouzeixPolynomialScalarCompanion_ball_center_le_polynomialSupNorm_closedBall

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R) :
    ‖crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball 0 R hR) p z‖ ≤
      polynomialSupNorm p (Metric.closedBall (0 : ℂ) R) := by
  exact
    norm_crouzeixPolynomialScalarCompanion_ball_center_le_polynomialSupNorm_closedBall
      0 hR p hz
