-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_centered_profile
-- name    : FirstPassageLinearTransport.rawFirstPassageTime_centered_profile
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:49:46.528097+00:00
-- url     : https://prove2.me/theorems/42268d35-78cc-4778-bf01-29d02631801c
-- title:
--   First Passage Linear Transport: raw First Passage Time centered profile
-- statement:
--   Raw first-passage time in the paper's normalization
--   `(3/2) c_* log(n/z)`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L538-L561
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L538-L561

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawFirstPassageTime_centered_profile
    {n k : ℕ} {z E : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z)
    (htube : ∀ i : ℕ, i ≤ rawTime n k → |rawLogDeviation n i| ≤ E) :
    |(rawFirstPassageTime n z : ℝ) -
        (3 / 2) * fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| ≤
      (3 / 2) * fixedPolylogClockCritical * (E + Real.log 2) := by sorry
