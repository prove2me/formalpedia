-- Prove2me | Theorems.Thm_ClassicalComplexWPT_norm_evalLast_le
-- name    : ClassicalComplexWPT.norm_evalLast_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:27.125396+00:00
-- url     : https://prove2.me/theorems/b2f12761-a5c3-4381-ba03-8a60e5d8c243
-- title:
--   Classical Complex WPT: norm eval Last le
-- statement:
--   The Classical Complex WPT construction uses the norm eval Last le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L45-L48
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L45-L48

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.norm_evalLast_le (n k : ℕ) : ‖evalLast n k‖ ≤ 1 := by sorry
