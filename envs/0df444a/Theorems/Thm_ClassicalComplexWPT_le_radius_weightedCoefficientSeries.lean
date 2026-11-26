-- Prove2me | Theorems.Thm_ClassicalComplexWPT_le_radius_weightedCoefficientSeries
-- name    : ClassicalComplexWPT.le_radius_weightedCoefficientSeries
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:48.47587+00:00
-- url     : https://prove2.me/theorems/53f8deb9-a749-4751-81ee-39d753b747e3
-- title:
--   Classical Complex WPT: le radius weighted Coefficient Series
-- statement:
--   The Classical Complex WPT construction uses the le radius weighted Coefficient Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L312-L322
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L312-L322

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.le_radius_weightedCoefficientSeries {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (s r : ℝ≥0)
    (hsr : (s + r : ℝ≥0∞) < p.radius) :
    (s : ℝ≥0∞) ≤ (weightedCoefficientSeries p r).radius := by sorry
