-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_parentRank_le_timeoutLowBudget
-- name    : FirstPassageLinearTransport.parentRank_le_timeoutLowBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:27.360428+00:00
-- url     : https://prove2.me/theorems/1a9ba70e-23ec-5b45-99ac-e0aa54d19de3
-- title:
--   First Passage Linear Transport: parent Rank le timeout Low Budget
-- statement:
--   The same rank budget for the real moving-low ratio used by the timeout
--   target.  No low certification package is involved.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L319-L338
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L319-L338

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.parentRank_le_timeoutLowBudget
    {K₀ : ℝ} {L m : ℕ} {rStar : ℚ}
    (hrStar : 0 < rStar)
    (hStar : (rStar : ℝ) ≤ movingLowRatio K₀ L) :
    (m : ℚ) ≤ ((timeoutTargetRank K₀ L m + 1 : ℕ) : ℚ) / rStar := by sorry
