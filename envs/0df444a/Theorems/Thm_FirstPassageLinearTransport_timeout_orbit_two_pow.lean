-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_timeout_orbit_two_pow
-- name    : FirstPassageLinearTransport.timeout_orbit_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:19:19.275605+00:00
-- url     : https://prove2.me/theorems/223e0d6c-fef3-5463-add3-43bdd72d5a7b
-- title:
--   First Passage Linear Transport: timeout orbit two pow
-- statement:
--   Exact halving orbit of a power of two up to its exponent.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean#L169-L180
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutCore.lean#L169-L180

import Definitions.Def_FirstPassageLinearTransport_MovingLowParameters
import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Topology

theorem FirstPassageLinearTransport.timeout_orbit_two_pow {m j : ℕ} (hj : j ≤ m) :
    orbit j (2 ^ m) = 2 ^ (m - j) := by sorry
