-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutTargetRank_lt_parent
-- name    : FirstPassageLinearTransport.timeoutTargetRank_lt_parent
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:38:50.927899+00:00
-- url     : https://prove2.me/theorems/c6660a3a-5978-4153-b133-a1934422cab1
-- title:
--   First Passage Linear Transport: timeout Target Rank lt parent
-- statement:
--   A moving ratio in `[0,1)` makes the timeout target strictly smaller than
--   every positive parent rank.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean#L54-L65
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean#L54-L65

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Topology

theorem FirstPassageLinearTransport.timeoutTargetRank_lt_parent
    {K₀ : ℝ} {L m : ℕ}
    (hr0 : 0 ≤ movingLowRatio K₀ L)
    (hr1 : movingLowRatio K₀ L < 1) (hm : 0 < m) :
    timeoutTargetRank K₀ L m < m := by sorry
