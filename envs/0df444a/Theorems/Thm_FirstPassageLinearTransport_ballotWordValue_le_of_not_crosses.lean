-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_le_of_not_crosses
-- name    : FirstPassageLinearTransport.ballotWordValue_le_of_not_crosses
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:37:18.793168+00:00
-- url     : https://prove2.me/theorems/f21ac46a-28e9-5497-808b-ea89a81a1b2e
-- title:
--   First Passage Linear Transport: ballot Word Value le of not crosses
-- statement:
--   The First Passage Linear Transport construction uses the ballot Word Value le of not crosses property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3041-L3063
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/FiniteBallot.lean#L3041-L3063

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.ballotWordValue_le_of_not_crosses :
    ∀ {u : ℝ} {r : ℕ} {z : ℝ} {v : Fin r → Bool},
      ¬crossesMultiplicativeFrom u r z v →
        ballotWordValue z v ≤ u := by sorry
