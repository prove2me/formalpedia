-- Prove2me | Theorems.Thm_ClassicalComplexWPT_radius_weightedLastCoeffs
-- name    : ClassicalComplexWPT.radius_weightedLastCoeffs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:33.543077+00:00
-- url     : https://prove2.me/theorems/6613fdac-c3e0-4c94-8a75-4ac45e07aadf
-- title:
--   Classical Complex WPT: radius weighted Last Coeffs
-- statement:
--   The Classical Complex WPT construction uses the radius weighted Last Coeffs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L142-L147
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L142-L147

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.radius_weightedLastCoeffs {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0) (x : Ambient n)
    (h : (‖x‖₊ + r : ℝ≥0∞) < p.radius) :
    (r : ℝ≥0∞) < (p.changeOrigin x).radius := by sorry
