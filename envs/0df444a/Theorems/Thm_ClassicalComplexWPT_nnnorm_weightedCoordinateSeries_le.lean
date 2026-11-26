-- Prove2me | Theorems.Thm_ClassicalComplexWPT_nnnorm_weightedCoordinateSeries_le
-- name    : ClassicalComplexWPT.nnnorm_weightedCoordinateSeries_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:58:55.024264+00:00
-- url     : https://prove2.me/theorems/448ae38c-2ff9-5cc1-aeef-f2e719f9dc11
-- title:
--   Classical Complex WPT: nnnorm weighted Coordinate Series le
-- statement:
--   The Classical Complex WPT construction uses the nnnorm weighted Coordinate Series le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L125-L131
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L125-L131

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.nnnorm_weightedCoordinateSeries_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (k l : ℕ) :
    ‖weightedCoordinateSeries p r k l‖₊ ≤
      ‖p.changeOriginSeries k l‖₊ * r ^ k := by sorry
