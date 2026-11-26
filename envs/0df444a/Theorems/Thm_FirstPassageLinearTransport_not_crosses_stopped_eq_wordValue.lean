-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_not_crosses_stopped_eq_wordValue
-- name    : FirstPassageLinearTransport.not_crosses_stopped_eq_wordValue
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:36:59.10409+00:00
-- url     : https://prove2.me/theorems/d15ec87b-0622-512e-9c78-d9df6b6d39c3
-- title:
--   First Passage Linear Transport: not crosses stopped eq word Value
-- statement:
--   The First Passage Linear Transport construction uses the not crosses stopped eq word Value property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2943-L2959
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L2943-L2959

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.not_crosses_stopped_eq_wordValue :
    ∀ {u : ℝ} {r : ℕ} {z : ℝ} {v : Fin r → Bool},
      ¬crossesMultiplicativeFrom u r z v →
        stoppedBallotValue u r z v = ballotWordValue z v := by sorry
