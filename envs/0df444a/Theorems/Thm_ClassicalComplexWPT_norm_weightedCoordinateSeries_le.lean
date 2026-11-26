-- Prove2me | Theorems.Thm_ClassicalComplexWPT_norm_weightedCoordinateSeries_le
-- name    : ClassicalComplexWPT.norm_weightedCoordinateSeries_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:30.607207+00:00
-- url     : https://prove2.me/theorems/294d624e-f6cd-4bba-899b-cd6e5fcab062
-- title:
--   Classical Complex WPT: norm weighted Coordinate Series le
-- statement:
--   The Classical Complex WPT construction uses the norm weighted Coordinate Series le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L110-L123
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L110-L123

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.norm_weightedCoordinateSeries_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k l : ℕ) :
    ‖weightedCoordinateSeries p r k l‖ ≤
      (r : ℝ) ^ k * ‖p.changeOriginSeries k l‖ := by sorry
