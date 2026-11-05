-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_nF_polyT
-- name    : CircuitLowerBound.Form.nF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:11:44.304928+00:00
-- url     : https://prove2.me/theorems/662d4366-57c2-47df-8d97-b11abdc92941
-- title:
--   Form: n F poly T
-- statement:
--   The Form construction uses the n F poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L502-L504
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L502-L504

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

theorem CircuitLowerBound.Form.nF_polyT {e : α → MCode} {L : α → ℕ} (he : PolyT e) (hL : PolyT L) : PolyT fun x => nF (e x) (L x) := by sorry
