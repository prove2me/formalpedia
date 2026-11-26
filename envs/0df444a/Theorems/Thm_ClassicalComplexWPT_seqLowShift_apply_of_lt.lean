-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqLowShift_apply_of_lt
-- name    : ClassicalComplexWPT.seqLowShift_apply_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:24.382336+00:00
-- url     : https://prove2.me/theorems/b0158bcd-e2fa-57b4-a3d2-f02b65bef2fb
-- title:
--   Classical Complex WPT: seq Low Shift apply of lt
-- statement:
--   The Classical Complex WPT construction uses the seq Low Shift apply of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L464-L469
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L464-L469

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqLowShift_apply_of_lt (d : ℕ) (f : L1Coeff ℕ) {n : ℕ} (hn : n < d) :
    seqLowShift d f n = 0 := by sorry
