-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
-- name    : FirstPassageLinearTransport.rawFirstPassageTime_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:28:26.307588+00:00
-- url     : https://prove2.me/theorems/8a4f2dd7-ec3a-4553-a2d1-b13fc8806991
-- title:
--   First Passage Linear Transport: raw First Passage Time self
-- statement:
--   The First Passage Linear Transport construction uses the raw First Passage Time self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L320-L324
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L320-L324

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawFirstPassageTime_self {n : ℕ} :
    rawFirstPassageTime n (n : ℝ) = 0 := by sorry
