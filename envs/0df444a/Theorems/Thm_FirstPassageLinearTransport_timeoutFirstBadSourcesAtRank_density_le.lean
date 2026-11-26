-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutFirstBadSourcesAtRank_density_le
-- name    : FirstPassageLinearTransport.timeoutFirstBadSourcesAtRank_density_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:26:52.134184+00:00
-- url     : https://prove2.me/theorems/0f73f0c5-bc00-4c46-8ab0-c1185de8fd4f
-- title:
--   First Passage Linear Transport: timeout First Bad Sources At Rank density le
-- statement:
--   Real rankwise density after timeout transport.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutProfile.lean#L24-L88
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutProfile.lean#L24-L88

import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
import Definitions.Def_FirstPassageLinearTransport_MovingSharpTail
import Definitions.Def_FirstPassageLinearTransport_TimeoutProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section

theorem FirstPassageLinearTransport.timeoutFirstBadSourcesAtRank_density_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S p : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hp : 1 ≤ p)
    (hnextPos : 0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : timeoutTargetRank K₀ L (p - 1) < p)
    (hpM : p < M)
    (hsmall : ((((p + 2 : ℕ) : ℚ) / rStar) /
      ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3)
    {H d : ℝ}
    (hTimes : ((timeoutFeasibleTimes P K₀ L M S p).card : ℝ) ≤ H)
    (hTarget :
      ((timeoutLandingBad K₀ L p).card : ℝ) / (2 : ℝ) ^ p ≤ d) :
    ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℝ) /
        (2 : ℝ) ^ M ≤
      H * (1 + 6 / (rStar : ℝ)) * ((p + 1 : ℕ) : ℝ) * d := by sorry
