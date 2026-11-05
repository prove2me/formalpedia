-- Prove2me | Theorems.Thm_CircuitLowerBound_Parse_length_gateW
-- name    : CircuitLowerBound.Parse.length_gateW
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:32:23.379875+00:00
-- url     : https://prove2.me/theorems/708cedae-7695-4fed-a5ec-943c156144c8
-- title:
--   Parse: length gate W
-- statement:
--   The word of a gate has 4 + 2W bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L65-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L65-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Parse
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Parse

theorem CircuitLowerBound.Parse.length_gateW (W : ℕ) (g : GateD) : (gateW W g).length = 4 + 2 * W := by sorry
