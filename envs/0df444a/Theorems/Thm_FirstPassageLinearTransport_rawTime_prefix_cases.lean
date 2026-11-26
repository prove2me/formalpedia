-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawTime_prefix_cases
-- name    : FirstPassageLinearTransport.rawTime_prefix_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:15.377709+00:00
-- url     : https://prove2.me/theorems/3f1cb877-fe90-5f8d-b115-eef2a290ced8
-- title:
--   First Passage Linear Transport: raw Time prefix cases
-- statement:
--   Every raw prefix is either a shortcut state or the unique intermediate
--   odd image immediately preceding the next shortcut state.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L70-L107
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L70-L107

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawTime_prefix_cases {n k i : ℕ} (hi : i ≤ rawTime n k) :
    ∃ j : ℕ, j ≤ k ∧
      (i = rawTime n j ∨
        (j < k ∧ orbit j n % 2 = 1 ∧ i = rawTime n j + 1)) := by sorry
