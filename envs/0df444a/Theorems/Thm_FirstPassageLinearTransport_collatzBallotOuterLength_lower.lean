-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzBallotOuterLength_lower
-- name    : FirstPassageLinearTransport.collatzBallotOuterLength_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:36:19.323408+00:00
-- url     : https://prove2.me/theorems/eb267f32-ac97-5c84-83b7-4f8d71015cc5
-- title:
--   First Passage Linear Transport: collatz Ballot Outer Length lower
-- statement:
--   The First Passage Linear Transport construction uses the collatz Ballot Outer Length lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2392-L2401
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2392-L2401

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzBallotOuterLength_lower {m : ℕ} (hm : 8 ≤ m) :
    (m : ℝ) / 8 ≤ collatzBallotOuterLength m := by sorry
