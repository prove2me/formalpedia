-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutRawTrajectorySupportConstant_pos
-- name    : FirstPassageLinearTransport.timeoutRawTrajectorySupportConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:21:07.279503+00:00
-- url     : https://prove2.me/theorems/01f6535c-9d72-53c9-873b-3a13801b9c07
-- title:
--   First Passage Linear Transport: timeout Raw Trajectory Support Constant pos
-- statement:
--   The First Passage Linear Transport construction uses the timeout Raw Trajectory Support Constant pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L260-L267
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L260-L267

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutRawTrajectorySupportConstant_pos
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutRawTrajectorySupportConstant P C := by sorry
