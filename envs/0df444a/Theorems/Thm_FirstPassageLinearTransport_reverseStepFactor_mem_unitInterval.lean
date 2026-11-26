-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_reverseStepFactor_mem_unitInterval
-- name    : FirstPassageLinearTransport.reverseStepFactor_mem_unitInterval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:49:45.110744+00:00
-- url     : https://prove2.me/theorems/724e509e-4b95-4e1c-aa0a-894e9758ae60
-- title:
--   First Passage Linear Transport: reverse Step Factor mem unit Interval
-- statement:
--   Every exact reverse step factor lies in the unit interval.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L683-L689
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L683-L689

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.reverseStepFactor_mem_unitInterval
    {n i : ℕ} (hn : 0 < n) :
    0 ≤ reverseStepFactor n i ∧ reverseStepFactor n i ≤ 1 := by sorry
