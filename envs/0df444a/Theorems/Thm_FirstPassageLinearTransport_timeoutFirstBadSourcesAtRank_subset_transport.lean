-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutFirstBadSourcesAtRank_subset_transport
-- name    : FirstPassageLinearTransport.timeoutFirstBadSourcesAtRank_subset_transport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:50.51629+00:00
-- url     : https://prove2.me/theorems/bc3d3282-eac6-551d-ab97-b49d02739833
-- title:
--   First Passage Linear Transport: timeout First Bad Sources At Rank subset transport
-- statement:
--   Every first timeout is a direct, loss-filtered transport into the actual
--   timeout target, using only feasible times of successful prefixes.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean#L86-L107
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutFirstBad.lean#L86-L107

import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Definitions.Def_FirstPassageLinearTransport_TimeSupportTransport
import Definitions.Def_FirstPassageLinearTransport_TimeoutFirstBad
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.timeoutFirstBadSourcesAtRank_subset_transport
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S p : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hM : 1 ≤ M) (hp : 1 ≤ p)
    (hnextPos : 0 < timeoutTargetRank K₀ L (p - 1))
    (hnextLt : timeoutTargetRank K₀ L (p - 1) < p) :
    timeoutFirstBadSourcesAtRank P K₀ L M S p ⊆
      lossFilteredTransportedSourcesAtTimes M (2 ^ p)
        (timeoutFeasibleTimes P K₀ L M S p)
        (timeoutLandingBad K₀ L p)
        (((p + 2 : ℕ) : ℚ) / rStar) := by sorry
