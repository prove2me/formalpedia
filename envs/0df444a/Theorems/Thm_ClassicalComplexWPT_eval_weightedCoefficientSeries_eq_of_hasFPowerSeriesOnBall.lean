-- Prove2me | Theorems.Thm_ClassicalComplexWPT_eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesOnBall
-- name    : ClassicalComplexWPT.eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesOnBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:51.451866+00:00
-- url     : https://prove2.me/theorems/cc441f93-472b-4893-8cf5-45e61c15b798
-- title:
--   Classical Complex WPT: eval weighted Coefficient Series eq of has FPower Series On Ball
-- statement:
--   If `p` represents `f` on a ball, weighted evaluation reconstructs `f` on
--   the explicit common convergence region.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedEvaluation.lean#L79-L100
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedEvaluation.lean#L79-L100

import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.eval_weightedCoefficientSeries_eq_of_hasFPowerSeriesOnBall {n : ℕ}
    {f : Ambient n → ℂ} (p : FormalMultilinearSeries ℂ (Ambient n) ℂ)
    (r : ℝ≥0) {ρ : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p 0 ρ)
    (hr0 : 0 < r) (hrp : (r : ℝ≥0∞) < p.radius)
    (z : Base n) (w : ℂ)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzw : (‖(z, (0 : ℂ))‖₊ + ‖((0 : Base n), w)‖₊ : ℝ≥0∞) < ρ)
    (hw : ‖w‖ < r) :
    evalL1PowerSeries ((weightedCoefficientSeries p r).sum z) ((r : ℂ)⁻¹ * w) =
      f (z, w) := by sorry
