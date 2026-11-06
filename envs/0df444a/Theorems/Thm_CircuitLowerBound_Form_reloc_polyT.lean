-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_reloc_polyT
-- name    : CircuitLowerBound.Form.reloc_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:59:38.700482+00:00
-- url     : https://prove2.me/theorems/bcd97d24-7413-4b61-b60c-1d75295cc552
-- title:
--   Form: reloc poly T
-- statement:
--   The Form construction uses the reloc poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L476-L479
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L476-L479

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

theorem CircuitLowerBound.Form.reloc_polyT {L N off : α → ℕ} {o : α → List ℕ} {C : α → List GateD} (hL : PolyT L) (hN : PolyT N) (ho : PolyT o) (hoff : PolyT off)
    (hC : PolyT C) : PolyT fun x => reloc (L x) (N x) (o x) (off x) (C x) := by sorry
