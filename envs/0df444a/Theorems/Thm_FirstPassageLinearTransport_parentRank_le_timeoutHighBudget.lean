-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_parentRank_le_timeoutHighBudget
-- name    : FirstPassageLinearTransport.parentRank_le_timeoutHighBudget
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:42:10.94509+00:00
-- url     : https://prove2.me/theorems/d16d1de1-fc5d-4f74-9fd0-bd38a2423349
-- title:
--   First Passage Linear Transport: parent Rank le timeout High Budget
-- statement:
--   A rational lower contraction dominated by the high ratio supplies the
--   rank budget needed by the reverse-loss induction.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L297-L315
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutRun.lean#L297-L315

import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_RankScaledLoss
import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.parentRank_le_timeoutHighBudget
    {rStar r : ℚ} (hrStar : 0 < rStar) (hStar : rStar ≤ r) (m : ℕ) :
    (m : ℚ) ≤ ((rationalTargetRank r m + 1 : ℕ) : ℚ) / rStar := by sorry
