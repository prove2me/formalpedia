-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawOrbit_two_eq_shortcut_of_odd
-- name    : FirstPassageLinearTransport.rawOrbit_two_eq_shortcut_of_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:58.331284+00:00
-- url     : https://prove2.me/theorems/15df9085-1458-523f-9e38-7dd6815c3ee5
-- title:
--   First Passage Linear Transport: raw Orbit two eq shortcut of odd
-- statement:
--   One odd shortcut step is exactly two raw steps.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L50-L55
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L50-L55

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.rawOrbit_two_eq_shortcut_of_odd {n : ℕ} (hn : n % 2 = 1) :
    rawOrbit 2 n = shortcut n := by sorry
