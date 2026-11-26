-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawLogDeviation_rawTime
-- name    : FirstPassageLinearTransport.rawLogDeviation_rawTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:47:47.2646+00:00
-- url     : https://prove2.me/theorems/413da80d-662d-5d31-b439-7085f76460a9
-- title:
--   First Passage Linear Transport: raw Log Deviation raw Time
-- statement:
--   At a raw time corresponding exactly to a shortcut prefix, raw deviation
--   is shortcut deviation plus the centered odd-count correction.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L59-L66
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L59-L66

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawLogDeviation_rawTime (n j : ℕ) :
    rawLogDeviation n (rawTime n j) =
      shortcutLogDeviation n j + rawOddDeviationCoefficient *
        ((oddCount n j : ℝ) - (j : ℝ) / 2) := by sorry
