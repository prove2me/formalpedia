-- Prove2me | Theorems.Thm_ClassicalComplexWPT_radius_weightedCoefficientSeries_pos
-- name    : ClassicalComplexWPT.radius_weightedCoefficientSeries_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:41.551307+00:00
-- url     : https://prove2.me/theorems/b50ecec8-0f99-45cb-bbd7-02444f097720
-- title:
--   Classical Complex WPT: radius weighted Coefficient Series pos
-- statement:
--   The Classical Complex WPT construction uses the radius weighted Coefficient Series pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L324-L331
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L324-L331

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.radius_weightedCoefficientSeries_pos {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) :
    0 < (weightedCoefficientSeries p r).radius := by sorry
