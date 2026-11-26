-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawLogDeviation_intermediate
-- name    : FirstPassageLinearTransport.rawLogDeviation_intermediate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:14.056892+00:00
-- url     : https://prove2.me/theorems/719843a4-e5d0-4e57-8ffa-98b80f50c1a5
-- title:
--   First Passage Linear Transport: raw Log Deviation intermediate
-- statement:
--   The intermediate raw odd image differs from the following corresponding
--   raw-time deviation by one bounded raw step.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L128-L148
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L128-L148

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawLogDeviation_intermediate
    {n j : ℕ} (hn : 0 < n) (hodd : orbit j n % 2 = 1) :
    rawLogDeviation n (rawTime n j + 1) =
      rawLogDeviation n (rawTime n (j + 1)) +
        (1 - 2 * driftGap / 3) * Real.log 2 := by sorry
