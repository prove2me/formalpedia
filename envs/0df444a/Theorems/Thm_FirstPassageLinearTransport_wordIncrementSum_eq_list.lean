-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_eq_list
-- name    : FirstPassageLinearTransport.wordIncrementSum_eq_list
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:29:40.669776+00:00
-- url     : https://prove2.me/theorems/85766fe9-6342-4f62-a3af-804812df6613
-- title:
--   First Passage Linear Transport: word Increment Sum eq list
-- statement:
--   The First Passage Linear Transport construction uses the word Increment Sum eq list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1321-L1333
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L1321-L1333

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.wordIncrementSum_eq_list
    {r : ℕ} (x : Bool → ℝ) (v : Fin r → Bool) :
    wordIncrementSum x v = listIncrementSum x (List.ofFn v) := by sorry
