-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_seqDivisionRemainderGlobal
-- name    : ClassicalComplexWPT.analyticAt_seqDivisionRemainderGlobal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:06:35.841251+00:00
-- url     : https://prove2.me/theorems/e377d098-fafb-4ef9-8d7e-40f10814c31a
-- title:
--   Classical Complex WPT: analytic At seq Division Remainder Global
-- statement:
--   The Classical Complex WPT construction uses the analytic At seq Division Remainder Global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L681-L701
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L681-L701

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analyticAt_seqDivisionRemainderGlobal (d : ℕ)
    (pf : L1Coeff ℕ × L1Coeff ℕ) (hp : ‖pf.1‖ < 1) :
    AnalyticAt ℂ (seqDivisionRemainderGlobal d) pf := by sorry
