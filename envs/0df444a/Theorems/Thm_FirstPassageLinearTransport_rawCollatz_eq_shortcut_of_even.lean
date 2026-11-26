-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawCollatz_eq_shortcut_of_even
-- name    : FirstPassageLinearTransport.rawCollatz_eq_shortcut_of_even
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:15:05.178409+00:00
-- url     : https://prove2.me/theorems/a29cef8f-010c-4420-9bfd-41291f9799fc
-- title:
--   First Passage Linear Transport: raw Collatz eq shortcut of even
-- statement:
--   One even shortcut step is one raw step.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L45-L47
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L45-L47

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.rawCollatz_eq_shortcut_of_even {n : ℕ} (hn : n % 2 = 0) :
    rawCollatz n = shortcut n := by sorry
