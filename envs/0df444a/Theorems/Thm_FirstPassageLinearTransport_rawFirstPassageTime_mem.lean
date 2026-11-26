-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_mem
-- name    : FirstPassageLinearTransport.rawFirstPassageTime_mem
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:49:00.525797+00:00
-- url     : https://prove2.me/theorems/e9e380a6-833c-40cd-bf76-dcbfde8b3bd1
-- title:
--   First Passage Linear Transport: raw First Passage Time mem
-- statement:
--   The First Passage Linear Transport construction uses the raw First Passage Time mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L302-L307
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L302-L307

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawFirstPassageTime_mem
    {n i : ℕ} {z : ℝ} (hi : (rawOrbit i n : ℝ) ≤ z) :
    (rawOrbit (rawFirstPassageTime n z) n : ℝ) ≤ z := by sorry
