-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingSeparatedFailureEnvelope_card_le
-- name    : FirstPassageLinearTransport.shrinkingSeparatedFailureEnvelope_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:19:10.524951+00:00
-- url     : https://prove2.me/theorems/71874633-81a4-57be-a89f-32e918a8e181
-- title:
--   First Passage Linear Transport: shrinking Separated Failure Envelope card le
-- statement:
--   The First Passage Linear Transport construction uses the shrinking Separated Failure Envelope card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean#L48-L82
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean#L48-L82

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.shrinkingSeparatedFailureEnvelope_card_le
    (P : ShrinkingBarrierRunData) (M L S : ℕ) :
    (shrinkingSeparatedFailureEnvelope P M L S).card ≤
      (shellInitialWindowBad M (shrinkingHighTolerance P M M)).card +
      ∑ q ∈ Finset.Icc (S + 1) (M - 1),
        (shrinkingFirstBadSourcesAtRank P M S q).card +
      ∑ q ∈ Finset.Icc L S,
        (shrinkingFirstBadSourcesAtRank P M S q).card := by sorry
