-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_one_eq_exp_incrementSum
-- name    : FirstPassageLinearTransport.ballotWordValue_one_eq_exp_incrementSum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:29:57.8578+00:00
-- url     : https://prove2.me/theorems/b9b75ebb-7bba-56cf-b03f-6a8e5d06c1c0
-- title:
--   First Passage Linear Transport: ballot Word Value one eq exp increment Sum
-- statement:
--   The First Passage Linear Transport construction uses the ballot Word Value one eq exp increment Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3171-L3183
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3171-L3183

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.ballotWordValue_one_eq_exp_incrementSum
    {r : ℕ} (v : Fin r → Bool) :
    ballotWordValue 1 v =
      Real.exp (wordIncrementSum collatzLogIncrement v) := by sorry
