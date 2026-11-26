-- Prove2me | Theorems.Thm_ClassicalComplexWPT_summable_changeOrigin_weighted_majorant
-- name    : ClassicalComplexWPT.summable_changeOrigin_weighted_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:31.864371+00:00
-- url     : https://prove2.me/theorems/3d951d80-b037-582f-99f9-5ab5cc56dead
-- title:
--   Classical Complex WPT: summable change Origin weighted majorant
-- statement:
--   The Classical Complex WPT construction uses the summable change Origin weighted majorant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L242-L310
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L242-L310

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.summable_changeOrigin_weighted_majorant {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (s r : ℝ≥0)
    (hsr : (s + r : ℝ≥0∞) < p.radius) :
    Summable (fun l : ℕ ↦
      (∑' k : ℕ, ‖p.changeOriginSeries k l‖₊ * r ^ k) * s ^ l) := by sorry
