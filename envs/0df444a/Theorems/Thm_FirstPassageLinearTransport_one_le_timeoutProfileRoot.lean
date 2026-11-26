-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_one_le_timeoutProfileRoot
-- name    : FirstPassageLinearTransport.one_le_timeoutProfileRoot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:27:42.269797+00:00
-- url     : https://prove2.me/theorems/5ade80ef-d654-546c-b688-40d9beb45221
-- title:
--   First Passage Linear Transport: one le timeout Profile Root
-- statement:
--   The First Passage Linear Transport construction uses the one le timeout Profile Root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L269-L277
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L269-L277

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.one_le_timeoutProfileRoot {M : ℕ} (hM : 1 ≤ M) :
    1 ≤ Real.sqrt (((M : ℝ) + 2) * Real.log ((M : ℝ) + 2)) := by sorry
