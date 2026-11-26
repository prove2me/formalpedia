-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_abs_shortcutLogDeviation_highStage_le_durationError
-- name    : FirstPassageLinearTransport.abs_shortcutLogDeviation_highStage_le_durationError
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:49:52.356304+00:00
-- url     : https://prove2.me/theorems/dd720cae-2ff7-5990-8a16-487cd6956bf3
-- title:
--   First Passage Linear Transport: abs shortcut Log Deviation high Stage le duration Error
-- statement:
--   The local tube of a certified high stage is no wider than the duration
--   error charged by the existing time-support potential.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L772-L818
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L772-L818

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.abs_shortcutLogDeviation_highStage_le_durationError
    (P : TimeoutHighRunData) {M m x j : ℕ}
    (hm0 : P.pHi.M0 ≤ m)
    (hxShell : x ∈ dyadicShell m)
    (hxGood : x ∈ initialWindowGood (timeoutHighTolerance P M m))
    (hj : j ≤ stageLength (timeoutHighSetup P M m) x) :
    |shortcutLogDeviation x j| ≤
      timeoutDurationError (timeoutHighTolerance P M m) m := by sorry
