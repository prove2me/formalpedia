-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivisionRemainder_apply_of_le
-- name    : ClassicalComplexWPT.seqDivisionRemainder_apply_of_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:06:36.174935+00:00
-- url     : https://prove2.me/theorems/bffac050-20a4-4f80-b5cc-34a1be4ca24f
-- title:
--   Classical Complex WPT: seq Division Remainder apply of le
-- statement:
--   The Classical Complex WPT construction uses the seq Division Remainder apply of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L769-L771
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L769-L771

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqDivisionRemainder_apply_of_le (d : ℕ) (p : L1Coeff ℕ)
    (hp : ‖p‖ < 1) (f : L1Coeff ℕ) {n : ℕ} (hn : d ≤ n) :
    seqDivisionRemainder d p hp f n = 0 := by sorry
