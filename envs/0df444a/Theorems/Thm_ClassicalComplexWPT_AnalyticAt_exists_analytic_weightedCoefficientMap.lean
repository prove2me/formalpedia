-- Prove2me | Theorems.Thm_ClassicalComplexWPT_AnalyticAt_exists_analytic_weightedCoefficientMap
-- name    : ClassicalComplexWPT.AnalyticAt.exists_analytic_weightedCoefficientMap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:18.411333+00:00
-- url     : https://prove2.me/theorems/b7a19d76-bebe-5d4e-b4c1-6c6c5ae34615
-- title:
--   Analytic At: exists analytic weighted Coefficient Map
-- statement:
--   The Analytic At construction uses the exists analytic weighted Coefficient Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L340-L348
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L340-L348

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.AnalyticAt.exists_analytic_weightedCoefficientMap {n : ℕ}
    {f : Ambient n → ℂ} (hf : AnalyticAt ℂ f 0) :
    ∃ (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0),
      HasFPowerSeriesAt f p 0 ∧ 0 < r ∧
        AnalyticAt ℂ (weightedCoefficientSeries p r).sum 0 := by sorry
