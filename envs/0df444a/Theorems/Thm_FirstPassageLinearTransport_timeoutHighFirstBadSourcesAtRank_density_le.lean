-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutHighFirstBadSourcesAtRank_density_le
-- name    : FirstPassageLinearTransport.timeoutHighFirstBadSourcesAtRank_density_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:26:22.122179+00:00
-- url     : https://prove2.me/theorems/83e26407-35db-58ce-85aa-becc2f2aa38b
-- title:
--   First Passage Linear Transport: timeout High First Bad Sources At Rank density le
-- statement:
--   Real rankwise density for a failed high certification.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean#L99-L158
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutEnvelope.lean#L99-L158

import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.timeoutHighFirstBadSourcesAtRank_density_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hqM : q < M)
    (hsmall : ((((q + 2 : ℕ) : ℚ) / rStar) /
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    {H d : ℝ}
    (hTimes : ((timeoutFeasibleTimes P K₀ L M S q).card : ℝ) ≤ H)
    (hTarget :
      ((landingBad q (timeoutHighTargetTolerance P M q)).card : ℝ) /
        (2 : ℝ) ^ q ≤ d) :
    ((timeoutHighFirstBadSourcesAtRank P K₀ L M S q).card : ℝ) /
        (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * d := by sorry
