-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawTime_strictMono
-- name    : FirstPassageLinearTransport.rawTime_strictMono
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:59.165921+00:00
-- url     : https://prove2.me/theorems/53084a41-4c7d-5dcb-b7bc-7af26d634a4e
-- title:
--   First Passage Linear Transport: raw Time strict Mono
-- statement:
--   Corresponding raw times are strictly increasing with shortcut time.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L110-L114
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutTrajectoryProfile.lean#L110-L114

import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Definitions.Def_FirstPassageLinearTransport_TimeoutTrajectoryProfile
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.rawTime_strictMono (n : ℕ) : StrictMono (rawTime n) := by sorry
