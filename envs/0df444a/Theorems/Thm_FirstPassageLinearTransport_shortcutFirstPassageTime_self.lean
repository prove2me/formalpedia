-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
-- name    : FirstPassageLinearTransport.shortcutFirstPassageTime_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:27:34.333856+00:00
-- url     : https://prove2.me/theorems/875b46a6-2440-5bf5-a5f4-c5809df98489
-- title:
--   First Passage Linear Transport: shortcut First Passage Time self
-- statement:
--   The First Passage Linear Transport construction uses the shortcut First Passage Time self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L314-L318
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L314-L318

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shortcutFirstPassageTime_self {n : ℕ} :
    shortcutFirstPassageTime n (n : ℝ) = 0 := by sorry
