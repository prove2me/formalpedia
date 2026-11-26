-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_sum_stoppedBallotValue_eq
-- name    : FirstPassageLinearTransport.sum_stoppedBallotValue_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:36:58.293118+00:00
-- url     : https://prove2.me/theorems/21772c01-9351-5280-b883-808c852da413
-- title:
--   First Passage Linear Transport: sum stopped Ballot Value eq
-- statement:
--   Finite stopped-tree mean identity.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2885-L2903
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2885-L2903

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.sum_stoppedBallotValue_eq :
    ∀ (u : ℝ) (r : ℕ) (z : ℝ),
      ∑ v : Fin r → Bool, stoppedBallotValue u r z v =
        (2 : ℝ) ^ r * z := by sorry
