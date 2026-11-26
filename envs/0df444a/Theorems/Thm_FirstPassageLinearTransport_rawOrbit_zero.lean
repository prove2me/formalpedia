-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
-- name    : FirstPassageLinearTransport.rawOrbit_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:03:23.377014+00:00
-- url     : https://prove2.me/theorems/a893b5c3-82ac-548a-b99a-586c7608b8bc
-- title:
--   First Passage Linear Transport: raw Orbit zero
-- statement:
--   The First Passage Linear Transport construction uses the raw Orbit zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L25-L26
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L25-L26

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.rawOrbit_zero (n : ℕ) : rawOrbit 0 n = n := by sorry
