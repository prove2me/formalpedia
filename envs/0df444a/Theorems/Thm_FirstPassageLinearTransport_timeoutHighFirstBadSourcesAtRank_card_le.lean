-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutHighFirstBadSourcesAtRank_card_le
-- name    : FirstPassageLinearTransport.timeoutHighFirstBadSourcesAtRank_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:43:39.400865+00:00
-- url     : https://prove2.me/theorems/25697a7d-ed55-467e-bae5-917835988c74
-- title:
--   First Passage Linear Transport: timeout High First Bad Sources At Rank card le
-- statement:
--   The First Passage Linear Transport construction uses the timeout High First Bad Sources At Rank card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean#L67-L96
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean#L67-L96

import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeoutHighFirstBadSourcesAtRank_card_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hqM : q < M)
    (hsmall : ((((q + 2 : ℕ) : ℚ) / rStar) /
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3) :
    ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℚ) ≤
      ((timeoutFeasibleTimes P K₀ L M S q).card : ℚ) *
        (1 + 3 * (((q + 2 : ℕ) : ℚ) / rStar)) *
          (2 : ℚ) ^ M / ((2 ^ q : ℕ) : ℚ) *
        ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℚ) := by sorry
