-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_drift_profile
-- name    : FirstPassageLinearTransport.rawFirstPassageTime_drift_profile
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:49:29.610094+00:00
-- url     : https://prove2.me/theorems/6ff3893a-76a7-4bf7-bcdc-7916e179a5e3
-- title:
--   First Passage Linear Transport: raw First Passage Time drift profile
-- statement:
--   A uniform raw trajectory tube gives the actual raw first-passage clock.
--   The first raw and shortcut passages reach the same landing.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L493-L534
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L493-L534

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawFirstPassageTime_drift_profile
    {n k : ℕ} {z E : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z)
    (htube : ∀ i : ℕ, i ≤ rawTime n k → |rawLogDeviation n i| ≤ E) :
    |(2 * driftGap / 3) * (rawFirstPassageTime n z : ℝ) * Real.log 2 -
        Real.log ((n : ℝ) / z)| ≤ E + Real.log 2 := by sorry
