-- Prove2me | Theorems.Thm_CircuitLowerBound_Parse_gateOfW_polyT
-- name    : CircuitLowerBound.Parse.gateOfW_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:13:42.462544+00:00
-- url     : https://prove2.me/theorems/4bccf8f6-be87-4d54-bd25-706febcfad3d
-- title:
--   Parse: gate Of W poly T
-- statement:
--   The gate written by a word.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L148-L149
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L148-L149

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

theorem CircuitLowerBound.Parse.gateOfW_polyT {W : α → ℕ} {b : α → List Bool} (hW : PolyT W) (hb : PolyT b) : PolyT fun a => gateOfW (W a) (b a) := by sorry
