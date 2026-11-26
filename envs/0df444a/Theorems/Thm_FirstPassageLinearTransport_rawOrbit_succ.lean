-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawOrbit_succ
-- name    : FirstPassageLinearTransport.rawOrbit_succ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T11:03:22.955492+00:00
-- url     : https://prove2.me/theorems/c8bdc5a0-c009-481d-85cd-c06dc5a7d42f
-- title:
--   First Passage Linear Transport: raw Orbit succ
-- statement:
--   The First Passage Linear Transport construction uses the raw Orbit succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L28-L30
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L28-L30

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.rawOrbit_succ (j n : ℕ) :
    rawOrbit (j + 1) n = rawCollatz (rawOrbit j n) := by sorry
