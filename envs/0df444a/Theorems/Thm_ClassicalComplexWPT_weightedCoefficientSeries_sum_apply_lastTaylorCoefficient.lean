-- Prove2me | Theorems.Thm_ClassicalComplexWPT_weightedCoefficientSeries_sum_apply_lastTaylorCoefficient
-- name    : ClassicalComplexWPT.weightedCoefficientSeries_sum_apply_lastTaylorCoefficient
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:01.005504+00:00
-- url     : https://prove2.me/theorems/870ac530-1767-5d60-9843-194856f019f5
-- title:
--   Classical Complex WPT: weighted Coefficient Series sum apply last Taylor Coefficient
-- statement:
--   The Classical Complex WPT construction uses the weighted Coefficient Series sum apply last Taylor Coefficient property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L387-L395
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L387-L395

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.weightedCoefficientSeries_sum_apply_lastTaylorCoefficient {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (z : Base n) (j : ℕ)
    (hr : (r : ℝ≥0∞) < p.radius)
    (hzq : z ∈ Metric.eball (0 : Base n) (weightedCoefficientSeries p r).radius)
    (hzp : (z, 0) ∈ Metric.eball (0 : Ambient n) p.radius) :
    (weightedCoefficientSeries p r).sum z j =
      (r : ℂ) ^ j * lastTaylorCoefficient p j z := by sorry
