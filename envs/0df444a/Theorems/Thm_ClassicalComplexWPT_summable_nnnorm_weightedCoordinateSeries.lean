-- Prove2me | Theorems.Thm_ClassicalComplexWPT_summable_nnnorm_weightedCoordinateSeries
-- name    : ClassicalComplexWPT.summable_nnnorm_weightedCoordinateSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:37.860213+00:00
-- url     : https://prove2.me/theorems/647f7c21-6d6e-484b-a999-35236f513050
-- title:
--   Classical Complex WPT: summable nnnorm weighted Coordinate Series
-- statement:
--   The Classical Complex WPT construction uses the summable nnnorm weighted Coordinate Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L197-L203
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L197-L203

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.summable_nnnorm_weightedCoordinateSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    Summable (fun k : ℕ ↦ ‖weightedCoordinateSeries p r k l‖₊) := by sorry
