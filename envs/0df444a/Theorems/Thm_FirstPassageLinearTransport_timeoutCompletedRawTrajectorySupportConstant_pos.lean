-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutCompletedRawTrajectorySupportConstant_pos
-- name    : FirstPassageLinearTransport.timeoutCompletedRawTrajectorySupportConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:32.08437+00:00
-- url     : https://prove2.me/theorems/ea005600-1ecf-5ec9-9b45-b1edbb5f7c42
-- title:
--   First Passage Linear Transport: timeout Completed Raw Trajectory Support Constant pos
-- statement:
--   The First Passage Linear Transport construction uses the timeout Completed Raw Trajectory Support Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1281-L1288
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L1281-L1288

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutCompletedRawTrajectorySupportConstant_pos
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutCompletedRawTrajectorySupportConstant P C := by sorry
