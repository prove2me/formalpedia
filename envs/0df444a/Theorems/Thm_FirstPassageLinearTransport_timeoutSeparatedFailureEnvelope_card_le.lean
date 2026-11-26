-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutSeparatedFailureEnvelope_card_le
-- name    : FirstPassageLinearTransport.timeoutSeparatedFailureEnvelope_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:26:29.114165+00:00
-- url     : https://prove2.me/theorems/0c2fefe6-0432-5f3a-9802-2a3b4380434c
-- title:
--   First Passage Linear Transport: timeout Separated Failure Envelope card le
-- statement:
--   The First Passage Linear Transport construction uses the timeout Separated Failure Envelope card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean#L172-L204
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean#L172-L204

import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeoutSeparatedFailureEnvelope_card_le
    (P : TimeoutHighRunData) (K₀ : ℝ) (M L S : ℕ) :
    (timeoutSeparatedFailureEnvelope P K₀ M L S).card ≤
      (shellInitialWindowBad M (timeoutHighTolerance P M M)).card +
      ∑ q ∈ Finset.Icc (S + 1) (M - 1),
        (timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card +
      ∑ p ∈ Finset.Icc (L + 1) S,
        (timeoutFirstBadSourcesAtRank P K₀ L M S p).card := by sorry
