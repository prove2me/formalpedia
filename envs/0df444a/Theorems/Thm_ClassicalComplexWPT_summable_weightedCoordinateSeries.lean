-- Prove2me | Theorems.Thm_ClassicalComplexWPT_summable_weightedCoordinateSeries
-- name    : ClassicalComplexWPT.summable_weightedCoordinateSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:27.292459+00:00
-- url     : https://prove2.me/theorems/fe7457cd-b4cd-57df-83ac-a031abaa603a
-- title:
--   Classical Complex WPT: summable weighted Coordinate Series
-- statement:
--   The Classical Complex WPT construction uses the summable weighted Coordinate Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L189-L195
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L189-L195

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.summable_weightedCoordinateSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    Summable (fun k : ℕ ↦ weightedCoordinateSeries p r k l) := by sorry
