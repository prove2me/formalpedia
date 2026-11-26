-- Prove2me | Theorems.Thm_ClassicalComplexWPT_summable_norm_l1_mul_pow
-- name    : ClassicalComplexWPT.summable_norm_l1_mul_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:33.106809+00:00
-- url     : https://prove2.me/theorems/e91ec0f9-d0fa-5965-bb3a-1fe9956494c7
-- title:
--   Classical Complex WPT: summable norm l1 mul pow
-- statement:
--   The Classical Complex WPT construction uses the summable norm l1 mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PowerSeries.lean#L112-L116
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PowerSeries.lean#L112-L116

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.summable_norm_l1_mul_pow (a : L1Sequence) {w : ℂ} (hw : ‖w‖ ≤ 1) :
    Summable (fun k : ℕ ↦ ‖a k * w ^ k‖) := by sorry
