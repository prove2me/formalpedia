-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivisionQuotientGlobal_eq
-- name    : ClassicalComplexWPT.seqDivisionQuotientGlobal_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:48.41005+00:00
-- url     : https://prove2.me/theorems/842fa384-1c36-5842-8c16-f09d06717845
-- title:
--   Classical Complex WPT: seq Division Quotient Global eq
-- statement:
--   The Classical Complex WPT construction uses the seq Division Quotient Global eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L652-L661
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L652-L661

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqDivisionQuotientGlobal_eq (d : ℕ) (p f : L1Coeff ℕ) (hp : ‖p‖ < 1) :
    seqDivisionQuotientGlobal d (p,f) = seqDivisionQuotient d p hp f := by sorry
