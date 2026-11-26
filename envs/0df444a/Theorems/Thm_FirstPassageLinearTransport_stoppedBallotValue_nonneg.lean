-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_nonneg
-- name    : FirstPassageLinearTransport.stoppedBallotValue_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:58:04.787812+00:00
-- url     : https://prove2.me/theorems/7db2735f-0a0f-5568-84d6-d0a84dad76d9
-- title:
--   First Passage Linear Transport: stopped Ballot Value nonneg
-- statement:
--   The First Passage Linear Transport construction uses the stopped Ballot Value nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2905-L2919
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2905-L2919

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.stoppedBallotValue_nonneg :
    ∀ {u : ℝ} {r : ℕ} {z : ℝ} {v : Fin r → Bool},
      0 ≤ z → 0 ≤ stoppedBallotValue u r z v := by sorry
