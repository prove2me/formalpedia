-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_check_polyT
-- name    : CircuitLowerBound.Form.check_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:59:39.827414+00:00
-- url     : https://prove2.me/theorems/eeb11dd0-371e-4510-bf1e-7133a0762931
-- title:
--   Form: check poly T
-- statement:
--   The Form construction uses the check poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L492-L496
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L492-L496

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_Lib_Int
import Definitions.Def_ToTuring_Lib_List3
import Definitions.Def_ToTuring_Lib_List2
import Definitions.Def_ToTuring_Lib_Unary
import Definitions.Def_ToTuring_Lib_Nat2
import Definitions.Def_ToTuring_Lib_Nat1b
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Form
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form
variable {α : Type} [Enc α]

theorem CircuitLowerBound.Form.check_polyT {L N : α → ℕ} {G C : α → List GateD} {o : α → List ℕ} (hL : PolyT L) (hN : PolyT N) (hG : PolyT G) (ho : PolyT o)
    (hC : PolyT C) : PolyT fun x => check (L x) (N x) (G x) (o x) (C x) := by sorry
