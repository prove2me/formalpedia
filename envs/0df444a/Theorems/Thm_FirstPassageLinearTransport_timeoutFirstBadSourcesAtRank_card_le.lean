-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutFirstBadSourcesAtRank_card_le
-- name    : FirstPassageLinearTransport.timeoutFirstBadSourcesAtRank_card_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:54.072813+00:00
-- url     : https://prove2.me/theorems/f2e9f8ee-6654-5359-899d-9993b86c5d77
-- title:
--   First Passage Linear Transport: timeout First Bad Sources At Rank card le
-- statement:
--   Exact rankwise timeout count with compressed feasible-time support.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean#L110-L142
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean#L110-L142

import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.timeoutFirstBadSourcesAtRank_card_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S p : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hp : 1 ≤ p)
    (hnextPos : 0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : timeoutTargetRank K₀ L (p - 1) < p)
    (hpM : p < M)
    (hsmall : ((((p + 2 : ℕ) : ℚ) / rStar) /
      ((2 ^ p : ℕ) : ℚ)) ≤ 1 / 3) :
    ((timeoutFirstBadSourcesAtRank P K₀ L M S p).card : ℚ) ≤
      ((timeoutFeasibleTimes P K₀ L M S p).card : ℚ) *
        (1 + 3 * (((p + 2 : ℕ) : ℚ) / rStar)) *
          (2 : ℚ) ^ M / ((2 ^ p : ℕ) : ℚ) *
        ((timeoutLandingBad K₀ L p).card : ℚ) := by sorry
