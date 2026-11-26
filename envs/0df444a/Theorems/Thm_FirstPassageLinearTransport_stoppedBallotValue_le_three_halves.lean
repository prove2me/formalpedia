-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_le_three_halves
-- name    : FirstPassageLinearTransport.stoppedBallotValue_le_three_halves
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:00.461929+00:00
-- url     : https://prove2.me/theorems/6a1994b3-7471-41e5-bdf2-31df516d9d50
-- title:
--   First Passage Linear Transport: stopped Ballot Value le three halves
-- statement:
--   A first crossing overshoots the open barrier by at most the upward
--   multiplier `3/2`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2923-L2941
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2923-L2941

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stoppedBallotValue_le_three_halves :
    ∀ {u : ℝ} {r : ℕ} {z : ℝ} {v : Fin r → Bool},
      0 ≤ u → 0 ≤ z → z ≤ 3 * u / 2 →
        stoppedBallotValue u r z v ≤ 3 * u / 2 := by sorry
