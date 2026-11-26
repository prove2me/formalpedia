-- Prove2me | Theorems.Thm_ClassicalComplexWPT_nnnorm_weightedCoefficientSeries_le
-- name    : ClassicalComplexWPT.nnnorm_weightedCoefficientSeries_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:25.381297+00:00
-- url     : https://prove2.me/theorems/670fd212-0992-5002-8902-e293a4e807a9
-- title:
--   Classical Complex WPT: nnnorm weighted Coefficient Series le
-- statement:
--   The Classical Complex WPT construction uses the nnnorm weighted Coefficient Series le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L205-L220
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L205-L220

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.nnnorm_weightedCoefficientSeries_le {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) :
    ‖weightedCoefficientSeries p r l‖₊ ≤
      ∑' k : ℕ, ‖p.changeOriginSeries k l‖₊ * r ^ k := by sorry
