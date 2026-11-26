-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_scaledReverseLoss_le
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.scaledReverseLoss_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:21:07.011318+00:00
-- url     : https://prove2.me/theorems/18b9caed-c972-5fc8-870d-dd211d462fa6
-- title:
--   Timeout Recertification Run: scaled Reverse Loss le
-- statement:
--   Complete sourcewise reverse-loss budget for the timeout route.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L374-L381
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L374-L381

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_scaledReverseLoss_le

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.scaledReverseLoss_le
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S n elapsed q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    scaledReverseLoss (2 ^ q) n elapsed ≤ ((q + 2 : ℕ) : ℚ) / rStar := by sorry
