-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_centered_profile
-- name    : FirstPassageLinearTransport.shortcutFirstPassageTime_centered_profile
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:48:50.379703+00:00
-- url     : https://prove2.me/theorems/7c81942a-b7d8-57b5-a6b3-069e13b35458
-- title:
--   First Passage Linear Transport: shortcut First Passage Time centered profile
-- statement:
--   The same profile in the paper's clock normalization
--   `c_* = 1 / (driftGap * log 2)`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L467-L489
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L467-L489

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shortcutFirstPassageTime_centered_profile
    {n k : ℕ} {z E : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z)
    (htube : ∀ j : ℕ, j ≤ k → |shortcutLogDeviation n j| ≤ E) :
    |(shortcutFirstPassageTime n z : ℝ) -
        fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| ≤
      fixedPolylogClockCritical * (E + Real.log 2) := by sorry
