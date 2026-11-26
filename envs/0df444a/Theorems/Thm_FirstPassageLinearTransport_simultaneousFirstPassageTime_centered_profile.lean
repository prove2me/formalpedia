-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_simultaneousFirstPassageTime_centered_profile
-- name    : FirstPassageLinearTransport.simultaneousFirstPassageTime_centered_profile
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:29.64633+00:00
-- url     : https://prove2.me/theorems/3abc4023-081a-484f-90d6-5a88ff447919
-- title:
--   First Passage Linear Transport: simultaneous First Passage Time centered profile
-- statement:
--   Uniform shortcut and raw tubes give simultaneous actual first-passage
--   profiles to every level between the selected landing and the source.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L565-L614
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L565-L614

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.simultaneousFirstPassageTime_centered_profile
    {n k ell : ℕ} {z Eshort Eraw : ℝ}
    (hn : 0 < n)
    (hzLanding : (orbit k n : ℝ) ≤ z)
    (hzSource : z ≤ (n : ℝ))
    (hell : ell = rawTime n k)
    (hshortcut : ∀ j : ℕ, j ≤ k →
      |shortcutLogDeviation n j| ≤ Eshort)
    (hraw : ∀ i : ℕ, i ≤ ell →
      |rawLogDeviation n i| ≤ Eraw) :
    |(shortcutFirstPassageTime n z : ℝ) -
        fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| +
      |(rawFirstPassageTime n z : ℝ) -
        (3 / 2) * fixedPolylogClockCritical * Real.log ((n : ℝ) / z)| ≤
        fixedPolylogClockCritical * (Eshort + Real.log 2) +
          (3 / 2) * fixedPolylogClockCritical * (Eraw + Real.log 2) ∧
      rawOrbit (rawFirstPassageTime n z) n =
        orbit (shortcutFirstPassageTime n z) n := by sorry
