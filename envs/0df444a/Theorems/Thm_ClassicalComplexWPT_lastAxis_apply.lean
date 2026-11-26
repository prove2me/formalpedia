-- Prove2me | Theorems.Thm_ClassicalComplexWPT_lastAxis_apply
-- name    : ClassicalComplexWPT.lastAxis_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:56:44.525413+00:00
-- url     : https://prove2.me/theorems/9ebbfeea-b2b9-4fb7-bcf0-7878b322f2bc
-- title:
--   Classical Complex WPT: last Axis apply
-- statement:
--   The Classical Complex WPT construction uses the last Axis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L21-L21
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/AnalyticSeries.lean#L21-L21

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
set_option autoImplicit true
open ClassicalComplexWPT

theorem ClassicalComplexWPT.lastAxis_apply (n : ℕ) (w : ℂ) : lastAxis n w = (0, w) := by sorry

attribute [defeq] ClassicalComplexWPT.lastAxis_apply
