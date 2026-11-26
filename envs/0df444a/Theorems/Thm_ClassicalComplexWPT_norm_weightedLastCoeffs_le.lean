-- Prove2me | Theorems.Thm_ClassicalComplexWPT_norm_weightedLastCoeffs_le
-- name    : ClassicalComplexWPT.norm_weightedLastCoeffs_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:49.829859+00:00
-- url     : https://prove2.me/theorems/68b85e55-ebce-5627-ac39-f7c91beff107
-- title:
--   Classical Complex WPT: norm weighted Last Coeffs le
-- statement:
--   The Classical Complex WPT construction uses the norm weighted Last Coeffs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L426-L450
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L426-L450

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.norm_weightedLastCoeffs_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (hr : (r : ℝ≥0∞) < (p.changeOrigin x).radius) :
    ‖weightedLastCoeffs p r x hr‖ ≤
      ∑' k : ℕ, ‖p.changeOrigin x k‖ * (r : ℝ) ^ k := by sorry
