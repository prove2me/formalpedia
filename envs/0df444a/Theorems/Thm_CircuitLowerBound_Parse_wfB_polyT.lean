-- Prove2me | Theorems.Thm_CircuitLowerBound_Parse_wfB_polyT
-- name    : CircuitLowerBound.Parse.wfB_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:17:40.723203+00:00
-- url     : https://prove2.me/theorems/daa67e45-f1fa-4303-9a7e-f5e910aacfdd
-- title:
--   Parse: wf B poly T
-- statement:
--   The test.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L156-L157
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Parse.lean#L156-L157

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

theorem CircuitLowerBound.Parse.wfB_polyT {n : α → ℕ} {C : α → List GateD} (hn : PolyT n) (hC : PolyT C) : PolyT fun a => wfB (n a) (C a) := by sorry
