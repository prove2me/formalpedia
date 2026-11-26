-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_abs_rawLogDeviation_rawTime_le
-- name    : FirstPassageLinearTransport.abs_rawLogDeviation_rawTime_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:48:19.278879+00:00
-- url     : https://prove2.me/theorems/6e91301e-3e5b-5901-a262-2211f3478d20
-- title:
--   First Passage Linear Transport: abs raw Log Deviation raw Time le
-- statement:
--   Corresponding raw times inherit the shortcut and odd-count tubes.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L151-L163
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L151-L163

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.abs_rawLogDeviation_rawTime_le
    {n j : ℕ} {E F : ℝ}
    (hshortcut : |shortcutLogDeviation n j| ≤ E)
    (hodd : |(oddCount n j : ℝ) - (j : ℝ) / 2| ≤ F) :
    |rawLogDeviation n (rawTime n j)| ≤
      E + rawOddDeviationCoefficient * F := by sorry
