-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_collatzBallotMiddleLength_lower
-- name    : FirstPassageLinearTransport.collatzBallotMiddleLength_lower
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:36:20.701967+00:00
-- url     : https://prove2.me/theorems/13988786-e8a3-4d9b-b762-b3741191b99b
-- title:
--   First Passage Linear Transport: collatz Ballot Middle Length lower
-- statement:
--   The First Passage Linear Transport construction uses the collatz Ballot Middle Length lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2403-L2411
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2403-L2411

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.collatzBallotMiddleLength_lower {m : ℕ} (hm : 8 ≤ m) :
    (m : ℝ) / 4 ≤ collatzBallotMiddleLength m := by sorry
