-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcutLogDeviation_add
-- name    : FirstPassageLinearTransport.shortcutLogDeviation_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:31:08.72248+00:00
-- url     : https://prove2.me/theorems/2050bc16-753b-49ee-af67-d482f95b1395
-- title:
--   First Passage Linear Transport: shortcut Log Deviation add
-- statement:
--   Logarithmic deviations split exactly when shortcut segments are
--   concatenated.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L49-L55
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L49-L55

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shortcutLogDeviation_add (n k j : ℕ) :
    shortcutLogDeviation n (j + k) =
      shortcutLogDeviation n k + shortcutLogDeviation (orbit k n) j := by sorry
