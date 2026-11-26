-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_landingBand
-- name    : FirstPassageLinearTransport.shortcutFirstPassageTime_landingBand
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:27:51.098906+00:00
-- url     : https://prove2.me/theorems/8d37259e-ec2f-5cd0-a089-1cc26b9a526e
-- title:
--   First Passage Linear Transport: shortcut First Passage Time landing Band
-- statement:
--   A nontrivial first downward crossing lands within a factor two of the
--   crossed real level.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L328-L361
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L328-L361

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shortcutFirstPassageTime_landingBand
    {n k : ℕ} {z : ℝ}
    (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z) :
    z < 2 * (orbit (shortcutFirstPassageTime n z) n : ℝ) ∧
      (orbit (shortcutFirstPassageTime n z) n : ℝ) ≤ z := by sorry
