-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_orbit_le_two_pow_mul
-- name    : FirstPassageLinearTransport.orbit_le_two_pow_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:26:41.606771+00:00
-- url     : https://prove2.me/theorems/3a3b7c5e-7957-44a4-9dc7-85a4b3efa45c
-- title:
--   First Passage Linear Transport: orbit le two pow mul
-- statement:
--   The First Passage Linear Transport construction uses the orbit le two pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L34-L42
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L34-L42

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.orbit_le_two_pow_mul (j n : ℕ) : orbit j n ≤ 2 ^ j * n := by sorry
