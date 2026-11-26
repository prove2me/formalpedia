-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
-- name    : FirstPassageLinearTransport.stoppedBallotValue_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:33.057572+00:00
-- url     : https://prove2.me/theorems/7b91fd26-0116-4589-816c-627908eafceb
-- title:
--   First Passage Linear Transport: stopped Ballot Value cons
-- statement:
--   The First Passage Linear Transport construction uses the stopped Ballot Value cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2877-L2882
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2877-L2882

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stoppedBallotValue_cons
    {u z : ℝ} {r : ℕ} (b : Bool) (w : Fin r → Bool) :
    stoppedBallotValue u (r + 1) z (Fin.cons b w) =
      if u < z then z else
        stoppedBallotValue u r (z * ballotMultiplier b) w := by sorry
