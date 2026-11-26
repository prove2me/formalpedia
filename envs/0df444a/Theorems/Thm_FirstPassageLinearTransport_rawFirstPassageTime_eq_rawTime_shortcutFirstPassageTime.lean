-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_eq_rawTime_shortcutFirstPassageTime
-- name    : FirstPassageLinearTransport.rawFirstPassageTime_eq_rawTime_shortcutFirstPassageTime
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:32:27.617446+00:00
-- url     : https://prove2.me/theorems/b60845ed-2b95-48fd-9f6b-917f842f9016
-- title:
--   First Passage Linear Transport: raw First Passage Time eq raw Time shortcut First Passage Time
-- statement:
--   Raw and shortcut first passages to an intervening level reach the same
--   state.  The raw clock is the exact raw time corresponding to the shortcut
--   first passage.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L366-L432
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L366-L432

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawFirstPassageTime_eq_rawTime_shortcutFirstPassageTime
    {n k : ℕ} {z : ℝ}
    (hn : 0 < n) (hzStart : z < (n : ℝ))
    (hk : (orbit k n : ℝ) ≤ z) :
    rawFirstPassageTime n z =
        rawTime n (shortcutFirstPassageTime n z) ∧
      rawOrbit (rawFirstPassageTime n z) n =
        orbit (shortcutFirstPassageTime n z) n := by sorry
