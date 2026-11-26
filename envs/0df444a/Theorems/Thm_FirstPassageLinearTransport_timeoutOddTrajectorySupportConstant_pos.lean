-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutOddTrajectorySupportConstant_pos
-- name    : FirstPassageLinearTransport.timeoutOddTrajectorySupportConstant_pos
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:50:16.717041+00:00
-- url     : https://prove2.me/theorems/962e414a-af7b-51f4-8fd0-31ba55d6af9f
-- title:
--   First Passage Linear Transport: timeout Odd Trajectory Support Constant pos
-- statement:
--   The First Passage Linear Transport construction uses the timeout Odd Trajectory Support Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1132-L1138
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1132-L1138

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutOddTrajectorySupportConstant_pos
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutOddTrajectorySupportConstant P C := by sorry
