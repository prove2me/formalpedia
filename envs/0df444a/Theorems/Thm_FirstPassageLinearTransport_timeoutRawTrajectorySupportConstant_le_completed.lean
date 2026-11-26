-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutRawTrajectorySupportConstant_le_completed
-- name    : FirstPassageLinearTransport.timeoutRawTrajectorySupportConstant_le_completed
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:51:09.338095+00:00
-- url     : https://prove2.me/theorems/66514e11-4123-41b8-9080-f897c3b6a1f6
-- title:
--   First Passage Linear Transport: timeout Raw Trajectory Support Constant le completed
-- statement:
--   The First Passage Linear Transport construction uses the timeout Raw Trajectory Support Constant le completed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1290-L1302
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1290-L1302

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutRawTrajectorySupportConstant_le_completed
    (P : TimeoutHighRunData) (C : ℝ) :
    timeoutRawTrajectorySupportConstant P C ≤
      timeoutCompletedRawTrajectorySupportConstant P C := by sorry
