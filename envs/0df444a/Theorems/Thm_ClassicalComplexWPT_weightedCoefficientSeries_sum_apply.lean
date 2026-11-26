-- Prove2me | Theorems.Thm_ClassicalComplexWPT_weightedCoefficientSeries_sum_apply
-- name    : ClassicalComplexWPT.weightedCoefficientSeries_sum_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:47.040429+00:00
-- url     : https://prove2.me/theorems/77da1899-c18a-570a-ba83-7ae571f69749
-- title:
--   Classical Complex WPT: weighted Coefficient Series sum apply
-- statement:
--   On the common convergence neighborhood, the `j`-th coordinate of the
--   `ℓ¹`-valued analytic sum is exactly the weighted moving Taylor coefficient.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L352-L385
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L352-L385

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.weightedCoefficientSeries_sum_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (z : Base n) (j : ℕ)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzp : baseInclusion n z ∈ Metric.eball (0 : Ambient n) p.radius) :
    (weightedCoefficientSeries p r).sum z j =
      (r : ℂ) ^ j *
        p.changeOrigin (baseInclusion n z) j (fun _ ↦ lastDirection n) := by sorry
