-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_weightedCoefficientSeries_sum
-- name    : ClassicalComplexWPT.analyticAt_weightedCoefficientSeries_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:58.09228+00:00
-- url     : https://prove2.me/theorems/102732cd-ec48-431d-af62-3f04060a2eed
-- title:
--   Classical Complex WPT: analytic At weighted Coefficient Series sum
-- statement:
--   The Classical Complex WPT construction uses the analytic At weighted Coefficient Series sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L333-L338
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L333-L338

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.analyticAt_weightedCoefficientSeries_sum {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) :
    AnalyticAt ℂ (weightedCoefficientSeries p r).sum 0 := by sorry
