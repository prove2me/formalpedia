-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_seqDivisionQuotientGlobal
-- name    : ClassicalComplexWPT.analyticAt_seqDivisionQuotientGlobal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:43.902404+00:00
-- url     : https://prove2.me/theorems/819c8dab-5c47-5089-bfdb-49aacdbbae2e
-- title:
--   Classical Complex WPT: analytic At seq Division Quotient Global
-- statement:
--   The Classical Complex WPT construction uses the analytic At seq Division Quotient Global property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L663-L669
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L663-L669

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.analyticAt_seqDivisionQuotientGlobal (d : ℕ)
    (pf : L1Coeff ℕ × L1Coeff ℕ) (hp : ‖pf.1‖ < 1) :
    AnalyticAt ℂ (seqDivisionQuotientGlobal d) pf := by sorry
