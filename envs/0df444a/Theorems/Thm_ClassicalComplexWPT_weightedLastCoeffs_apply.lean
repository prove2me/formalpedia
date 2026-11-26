-- Prove2me | Theorems.Thm_ClassicalComplexWPT_weightedLastCoeffs_apply
-- name    : ClassicalComplexWPT.weightedLastCoeffs_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:17.316882+00:00
-- url     : https://prove2.me/theorems/92652bc6-5797-4e13-9f21-171eae854db2
-- title:
--   Classical Complex WPT: weighted Last Coeffs apply
-- statement:
--   The Classical Complex WPT construction uses the weighted Last Coeffs apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L420-L424
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L420-L424

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.weightedLastCoeffs_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (hr : (r : ℝ≥0∞) < (p.changeOrigin x).radius) (k : ℕ) :
    weightedLastCoeffs p r x hr k =
      (r : ℂ) ^ k * p.changeOrigin x k (fun _ ↦ lastDirection n) := by sorry

attribute [defeq] ClassicalComplexWPT.weightedLastCoeffs_apply
