-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutOddTrajectorySupportConstant_le_completed
-- name    : FirstPassageLinearTransport.timeoutOddTrajectorySupportConstant_le_completed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:32:10.411688+00:00
-- url     : https://prove2.me/theorems/ddb7e298-2411-5627-9891-430a2d11c254
-- title:
--   First Passage Linear Transport: timeout Odd Trajectory Support Constant le completed
-- statement:
--   The First Passage Linear Transport construction uses the timeout Odd Trajectory Support Constant le completed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1195-L1200
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1195-L1200

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutOddTrajectorySupportConstant_le_completed
    (P : TimeoutHighRunData) (C : ℝ) :
    timeoutOddTrajectorySupportConstant P C ≤
      timeoutCompletedOddTrajectorySupportConstant P C := by sorry
