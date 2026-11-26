-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqLowShift_apply_of_le
-- name    : ClassicalComplexWPT.seqLowShift_apply_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:11.159175+00:00
-- url     : https://prove2.me/theorems/a9ebabe8-b5aa-4974-88df-9da1c7aff2d5
-- title:
--   Classical Complex WPT: seq Low Shift apply of le
-- statement:
--   The Classical Complex WPT construction uses the seq Low Shift apply of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L471-L476
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L471-L476

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqLowShift_apply_of_le (d : ℕ) (f : L1Coeff ℕ) {n : ℕ} (hn : d ≤ n) :
    seqLowShift d f n = f (n - d) := by sorry
