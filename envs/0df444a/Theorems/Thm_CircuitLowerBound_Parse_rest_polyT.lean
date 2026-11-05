-- Prove2me | Theorems.Thm_CircuitLowerBound_Parse_rest_polyT
-- name    : CircuitLowerBound.Parse.rest_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:14:22.588302+00:00
-- url     : https://prove2.me/theorems/50f433d9-0af4-40d3-8252-2eccfb1d5a9d
-- title:
--   Parse: rest poly T
-- statement:
--   The word after its first ones and the zero that ends them.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L144-L145
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L144-L145

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Parse
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Parse
variable {α : Type} [Enc α]

theorem CircuitLowerBound.Parse.rest_polyT {x : α → List Bool} (hx : PolyT x) : PolyT fun a => rest (x a) := by sorry
