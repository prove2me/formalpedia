-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawOrbit_rawTime_add_one_eq_two_mul
-- name    : FirstPassageLinearTransport.rawOrbit_rawTime_add_one_eq_two_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:30:18.898884+00:00
-- url     : https://prove2.me/theorems/3a63f771-dd4e-566e-97fe-e6c2c2bf21f5
-- title:
--   First Passage Linear Transport: raw Orbit raw Time add one eq two mul
-- statement:
--   The only non-shortcut raw state is twice the following shortcut state.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L117-L124
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L117-L124

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawOrbit_rawTime_add_one_eq_two_mul
    {n j : ℕ} (hodd : orbit j n % 2 = 1) :
    rawOrbit (rawTime n j + 1) n = 2 * orbit (j + 1) n := by sorry
