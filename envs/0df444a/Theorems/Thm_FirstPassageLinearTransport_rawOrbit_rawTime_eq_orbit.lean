-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_rawOrbit_rawTime_eq_orbit
-- name    : FirstPassageLinearTransport.rawOrbit_rawTime_eq_orbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:26:28.870194+00:00
-- url     : https://prove2.me/theorems/9f9d3f0d-1217-54a9-99f4-2e4e0331fb34
-- title:
--   First Passage Linear Transport: raw Orbit raw Time eq orbit
-- statement:
--   The raw iterate at `k + oddCount n k` is the `k`-th shortcut iterate.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L61-L83
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/RawDynamics.lean#L61-L83

import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
set_option autoImplicit true
open FirstPassageLinearTransport

theorem FirstPassageLinearTransport.rawOrbit_rawTime_eq_orbit (n k : ℕ) :
    rawOrbit (rawTime n k) n = orbit k n := by sorry
