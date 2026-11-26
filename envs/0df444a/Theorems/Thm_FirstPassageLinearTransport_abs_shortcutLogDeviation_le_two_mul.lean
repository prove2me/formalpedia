-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_abs_shortcutLogDeviation_le_two_mul
-- name    : FirstPassageLinearTransport.abs_shortcutLogDeviation_le_two_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:32:46.506345+00:00
-- url     : https://prove2.me/theorems/6059fc05-efcf-4b36-ad8d-0655a3b28b77
-- title:
--   First Passage Linear Transport: abs shortcut Log Deviation le two mul
-- statement:
--   The elementary one-step bounds give a coarse logarithmic tube without
--   any parity certificate.  This is used only inside the short low-rank tail.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L647-L680
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L647-L680

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.abs_shortcutLogDeviation_le_two_mul
    {n j : ℕ} (hn : 0 < n) :
    |shortcutLogDeviation n j| ≤ 2 * (j : ℝ) := by sorry
