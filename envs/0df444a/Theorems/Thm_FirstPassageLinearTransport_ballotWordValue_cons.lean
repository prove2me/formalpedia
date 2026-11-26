-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
-- name    : FirstPassageLinearTransport.ballotWordValue_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:27:16.803878+00:00
-- url     : https://prove2.me/theorems/d75bd276-a4ff-57ed-8f4b-ad96d12733d5
-- title:
--   First Passage Linear Transport: ballot Word Value cons
-- statement:
--   The First Passage Linear Transport construction uses the ballot Word Value cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2860-L2865
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2860-L2865

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.ballotWordValue_cons
    {r : ℕ} (z : ℝ) (b : Bool) (w : Fin r → Bool) :
    ballotWordValue z (Fin.cons b w) =
      ballotWordValue (z * ballotMultiplier b) w := by sorry
