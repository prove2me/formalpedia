-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeout_switch_sq_le_source_potential
-- name    : FirstPassageLinearTransport.timeout_switch_sq_le_source_potential
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:18:47.520851+00:00
-- url     : https://prove2.me/theorems/b0260721-afe9-4d06-b048-55dfd0e38601
-- title:
--   First Passage Linear Transport: timeout switch sq le source potential
-- statement:
--   At the source rank the timeout potential contains the complete `S²`
--   reserve.  This elementary lower bound is useful when a terminal rank below
--   the switch has to be absorbed into the common time corridor.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L174-L189
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTimeSupport.lean#L174-L189

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.timeout_switch_sq_le_source_potential
    (P : TimeoutHighRunData) {M S : ℕ} (hS : S < M + 1) :
    (S : ℝ) ^ 2 ≤ timeoutTimePotential P M S (M + 1) := by sorry
