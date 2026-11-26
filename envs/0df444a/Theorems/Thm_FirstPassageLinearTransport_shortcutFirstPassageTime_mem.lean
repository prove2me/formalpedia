-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_mem
-- name    : FirstPassageLinearTransport.shortcutFirstPassageTime_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:29.760618+00:00
-- url     : https://prove2.me/theorems/b5d9fadf-ffdc-5224-ac5b-d6a1c87ff13a
-- title:
--   First Passage Linear Transport: shortcut First Passage Time mem
-- statement:
--   The First Passage Linear Transport construction uses the shortcut First Passage Time mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L290-L295
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L290-L295

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shortcutFirstPassageTime_mem
    {n k : ℕ} {z : ℝ} (hk : (orbit k n : ℝ) ≤ z) :
    (orbit (shortcutFirstPassageTime n z) n : ℝ) ≤ z := by sorry
