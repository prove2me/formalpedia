-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_le
-- name    : FirstPassageLinearTransport.shortcutFirstPassageTime_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:28:31.69052+00:00
-- url     : https://prove2.me/theorems/ff74bf91-a41e-49c6-89b8-4c63824dc28d
-- title:
--   First Passage Linear Transport: shortcut First Passage Time le
-- statement:
--   The First Passage Linear Transport construction uses the shortcut First Passage Time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L297-L300
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L297-L300

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shortcutFirstPassageTime_le
    {n k : ℕ} {z : ℝ} (hk : (orbit k n : ℝ) ≤ z) :
    shortcutFirstPassageTime n z ≤ k := by sorry
