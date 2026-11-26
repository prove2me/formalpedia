-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_toCertifiedRankChain
-- name    : FirstPassageLinearTransport.TimeoutRecertificationRun.toCertifiedRankChain
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:42:31.54355+00:00
-- url     : https://prove2.me/theorems/23f48d49-480c-5b50-9d6b-320b6ac759f4
-- title:
--   Timeout Recertification Run: to Certified Rank Chain
-- statement:
--   Every timeout run is a rank-scaled chain for any fixed positive rational
--   contraction dominated by both the high and moving-low ratios.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L342-L371
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L342-L371

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Theorems.Thm_FirstPassageLinearTransport_MixedRecertificationRun_toCertifiedRankChain
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_toCertifiedRankChain

set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.TimeoutRecertificationRun.toCertifiedRankChain
    {P : TimeoutHighRunData} {K₀ : ℝ} {rStar : ℚ}
    {L M S n elapsed q : ℕ}
    (hrStar : 0 < rStar) (hStarHi : rStar ≤ P.rHi)
    (hStarLo : (rStar : ℝ) ≤ movingLowRatio K₀ L)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    CertifiedRankChain rStar n elapsed q := by sorry
