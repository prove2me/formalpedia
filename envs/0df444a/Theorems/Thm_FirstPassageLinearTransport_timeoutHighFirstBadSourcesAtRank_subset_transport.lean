-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutHighFirstBadSourcesAtRank_subset_transport
-- name    : FirstPassageLinearTransport.timeoutHighFirstBadSourcesAtRank_subset_transport
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:43:29.137572+00:00
-- url     : https://prove2.me/theorems/d6aeb516-5fb4-4628-9388-18408321636b
-- title:
--   First Passage Linear Transport: timeout High First Bad Sources At Rank subset transport
-- statement:
--   The First Passage Linear Transport construction uses the timeout High First Bad Sources At Rank subset transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean#L47-L65
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean#L47-L65

import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeoutHighFirstBadSourcesAtRank_subset_transport
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) :
    timeoutHighFirstBadSourcesAtRank P K₀ L M S q ⊆
      lossFilteredTransportedSourcesAtTimes M (2 ^ q)
        (timeoutFeasibleTimes P K₀ L M S q)
        (landingBad q (timeoutHighTargetTolerance P M q))
        (((q + 2 : ℕ) : ℚ) / rStar) := by sorry
