-- Prove2me | Theorems.Thm_CircuitLowerBound_Parse_length_flatten_gateW
-- name    : CircuitLowerBound.Parse.length_flatten_gateW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:33:17.95042+00:00
-- url     : https://prove2.me/theorems/1846f60a-b8e0-4110-ac4f-e0db14325c1e
-- title:
--   Parse: length flatten gate W
-- statement:
--   The words of the gates have |C|·(4 + 2W) bits together.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L95-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L95-L98

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Parse

theorem CircuitLowerBound.Parse.length_flatten_gateW (W : ℕ) (C : List GateD) : ((C.map (gateW W)).flatten).length = C.length * (4 + 2 * W) := by sorry
