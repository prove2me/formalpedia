-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shrinkingFirstBadSourcesAtRank_density_le
-- name    : FirstPassageLinearTransport.shrinkingFirstBadSourcesAtRank_density_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:19:20.909005+00:00
-- url     : https://prove2.me/theorems/dd0911f4-85df-5576-8102-a6508ebca8b3
-- title:
--   First Passage Linear Transport: shrinking First Bad Sources At Rank density le
-- statement:
--   Real rankwise density estimate after the support-sensitive transport
--   and the linear rank multiplier are applied.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean#L86-L145
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/ShrinkingProfile.lean#L86-L145

import Definitions.Def_FirstPassageLinearTransport_ShrinkingFirstBad
import Definitions.Def_FirstPassageLinearTransport_ShrinkingProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section

theorem FirstPassageLinearTransport.shrinkingFirstBadSourcesAtRank_density_le
    (P : ShrinkingBarrierRunData) {M S q : ℕ}
    (hqM : q < M)
    (hsmall : ((((q + 2 : ℕ) : ℚ) / P.rStar) /
      ((2 ^ q : ℕ) : ℚ)) ≤ 1 / 3)
    {H d : ℝ}
    (hTimes : ((shrinkingFeasibleTimes P M S q).card : ℝ) ≤ H)
    (hTarget :
      ((landingBad q (shrinkingTargetTolerance P M S q)).card : ℝ) /
        (2 : ℝ) ^ q ≤ d) :
    ((shrinkingFirstBadSourcesAtRank P M S q).card : ℝ) /
        (2 : ℝ) ^ M ≤
      H * (1 + 6 / (P.rStar : ℝ)) * ((q + 1 : ℕ) : ℝ) * d := by sorry
