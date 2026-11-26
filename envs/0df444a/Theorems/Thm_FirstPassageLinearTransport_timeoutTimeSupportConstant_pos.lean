-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeoutTimeSupportConstant_pos
-- name    : FirstPassageLinearTransport.timeoutTimeSupportConstant_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:17:47.606586+00:00
-- url     : https://prove2.me/theorems/2c736088-aaae-52b4-a1d2-70dceb259708
-- title:
--   First Passage Linear Transport: timeout Time Support Constant pos
-- statement:
--   The explicit timeout support constant is strictly positive.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L616-L632
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L616-L632

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeoutTimeSupportConstant_pos
    (P : TimeoutHighRunData) (C : ℝ) :
    0 < timeoutTimeSupportConstant P C := by sorry
