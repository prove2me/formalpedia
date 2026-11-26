-- Prove2me | Theorems.Thm_ClassicalComplexWPT_weightedCoefficientSeries_apply
-- name    : ClassicalComplexWPT.weightedCoefficientSeries_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:43.135147+00:00
-- url     : https://prove2.me/theorems/8f45c258-afeb-4b68-abd8-90fc1ffb0501
-- title:
--   Classical Complex WPT: weighted Coefficient Series apply
-- statement:
--   The Classical Complex WPT construction uses the weighted Coefficient Series apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L222-L240
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L222-L240

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.weightedCoefficientSeries_apply {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (l : ℕ) (v : Fin l → Base n) (j : ℕ) :
    weightedCoefficientSeries p r l v j =
      (r : ℂ) ^ j * (p.changeOriginSeries j l)
        (fun i ↦ baseInclusion n (v i)) (fun _ ↦ lastDirection n) := by sorry
