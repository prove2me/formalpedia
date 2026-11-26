-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawOrbit_add
-- name    : FirstPassageLinearTransport.rawOrbit_add
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:14:46.12451+00:00
-- url     : https://prove2.me/theorems/90208b0d-2bf6-4360-bbd4-b9ff93842c76
-- title:
--   First Passage Linear Transport: raw Orbit add
-- statement:
--   The First Passage Linear Transport construction uses the raw Orbit add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L32-L34
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L32-L34

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.rawOrbit_add (j k n : ℕ) :
    rawOrbit (j + k) n = rawOrbit j (rawOrbit k n) := by sorry
