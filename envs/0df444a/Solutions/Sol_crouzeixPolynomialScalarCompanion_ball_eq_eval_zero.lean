-- Prove2me | solution 1 for crouzeixPolynomialScalarCompanion_ball_eq_eval_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:40:05.116805+00:00
-- url     : https://prove2.me/submissions/be3731e2-66ec-4f44-8d4a-825f3cf306eb

import Definitions.Def_Operator_Crouzeix_AffineDisk
import Definitions.Def_Operator_Crouzeix_CircleAuxiliary
import Definitions.Def_Operator_Crouzeix_ScalarCompanion
import Definitions.Def_Operator_Crouzeix_SpectralAuxiliaryCenter
import Definitions.Def_Operator_Crouzeix_VonNeumann
import Definitions.Def_Operator_Crouzeix_ScalarCompanionCircle
import Theorems.Thm_crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center

set_option autoImplicit false
open Complex MeasureTheory Set
open scoped InnerProductSpace Interval Real
theorem _root_.solution
    {R : ℝ} (hR : 0 < R) (p : Polynomial ℂ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) R) :
    crouzeixPolynomialScalarCompanion
        (SmoothJordanDomain.ball 0 R hR) p z =
      star (Polynomial.eval 0 p) :=
  crouzeixPolynomialScalarCompanion_ball_center_eq_eval_center 0 hR p hz
