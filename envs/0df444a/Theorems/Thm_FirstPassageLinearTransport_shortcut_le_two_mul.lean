-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shortcut_le_two_mul
-- name    : FirstPassageLinearTransport.shortcut_le_two_mul
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:47:01.898297+00:00
-- url     : https://prove2.me/theorems/f4989e95-a30f-595d-873b-5c15ed22ba88
-- title:
--   First Passage Linear Transport: shortcut le two mul
-- statement:
--   The First Passage Linear Transport construction uses the shortcut le two mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L26-L32
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/TimeoutOrbitCeiling.lean#L26-L32

import Definitions.Def_FirstPassageLinearTransport_TimeoutEndpointAsymptotics
import Definitions.Def_FirstPassageLinearTransport_AsymptoticBounds
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shortcut_le_two_mul (n : ℕ) : shortcut n ≤ 2 * n := by sorry
