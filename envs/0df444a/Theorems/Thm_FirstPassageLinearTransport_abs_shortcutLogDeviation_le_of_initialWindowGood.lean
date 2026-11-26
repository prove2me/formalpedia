-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_abs_shortcutLogDeviation_le_of_initialWindowGood
-- name    : FirstPassageLinearTransport.abs_shortcutLogDeviation_le_of_initialWindowGood
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:40.51103+00:00
-- url     : https://prove2.me/theorems/db523f5c-6187-4034-8dd8-45c4e1126c40
-- title:
--   First Passage Linear Transport: abs shortcut Log Deviation le of initial Window Good
-- statement:
--   Every prefix of one certified high block lies in its deterministic
--   logarithmic tube.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L618-L643
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L618-L643

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.abs_shortcutLogDeviation_le_of_initialWindowGood
    {t : ℝ} {n j : ℕ}
    (hn : 0 < n)
    (hnGood : n ∈ initialWindowGood t)
    (hj : j ≤ Nat.log 2 n) :
    |shortcutLogDeviation n j| ≤ t * Real.log n := by sorry
