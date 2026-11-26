-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_parityBit_add
-- name    : FirstPassageLinearTransport.parityBit_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:03:47.51824+00:00
-- url     : https://prove2.me/theorems/0d32d1d2-18ce-5f06-8bf9-49d0597adfa8
-- title:
--   First Passage Linear Transport: parity Bit add
-- statement:
--   Parity bits shift with the source after a shortcut prefix.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L86-L89
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L86-L89

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.parityBit_add (n k j : ℕ) :
    parityBit n (k + j) = parityBit (orbit k n) j := by sorry
