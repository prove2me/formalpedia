-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_parentRank_le_commonTargetBudget
-- name    : FirstPassageLinearTransport.parentRank_le_commonTargetBudget
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:09:16.05864+00:00
-- url     : https://prove2.me/theorems/40771d9b-0214-5b6e-b811-d6108b7bcd82
-- title:
--   First Passage Linear Transport: parent Rank le common Target Budget
-- statement:
--   A floor target formed with `r` satisfies the parent-rank budget for every
--   positive common parameter `rStar ≤ r`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeRun.lean#L24-L45
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TwoRegimeRun.lean#L24-L45

import Definitions.Def_FirstPassageLinearTransport_TerminalProfile
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeRun
set_option autoImplicit true
open FirstPassageLinearTransport
noncomputable section

theorem FirstPassageLinearTransport.parentRank_le_commonTargetBudget
    {rStar r : ℚ} (hrStar : 0 < rStar) (hStar : rStar ≤ r) (m : ℕ) :
    (m : ℚ) ≤ ((rationalTargetRank r m + 1 : ℕ) : ℚ) / rStar := by sorry
