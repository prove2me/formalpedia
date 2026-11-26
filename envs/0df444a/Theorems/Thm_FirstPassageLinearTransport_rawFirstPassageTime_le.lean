-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_le
-- name    : FirstPassageLinearTransport.rawFirstPassageTime_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:40.488117+00:00
-- url     : https://prove2.me/theorems/9a8e2ddd-59b6-520e-9037-62bafac12f72
-- title:
--   First Passage Linear Transport: raw First Passage Time le
-- statement:
--   The First Passage Linear Transport construction uses the raw First Passage Time le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L309-L312
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L309-L312

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawFirstPassageTime_le
    {n i : ℕ} {z : ℝ} (hi : (rawOrbit i n : ℝ) ≤ z) :
    rawFirstPassageTime n z ≤ i := by sorry
