-- Prove2me | Theorems.Thm_ClassicalComplexWPT_norm_lastCoefficientSeries_le
-- name    : ClassicalComplexWPT.norm_lastCoefficientSeries_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:15.864263+00:00
-- url     : https://prove2.me/theorems/21c00672-e92e-5f73-87df-244036c8fe06
-- title:
--   Classical Complex WPT: norm last Coefficient Series le
-- statement:
--   The Classical Complex WPT construction uses the norm last Coefficient Series le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L82-L108
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L82-L108

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.norm_lastCoefficientSeries_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (k l : ℕ) :
    ‖lastCoefficientSeries p k l‖ ≤ ‖p.changeOriginSeries k l‖ := by sorry
