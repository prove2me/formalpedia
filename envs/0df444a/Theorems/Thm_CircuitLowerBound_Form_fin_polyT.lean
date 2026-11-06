-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_fin_polyT
-- name    : CircuitLowerBound.Form.fin_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:59:23.711559+00:00
-- url     : https://prove2.me/theorems/505e7e47-2def-42ad-b759-fceda2831436
-- title:
--   Form: fin poly T
-- statement:
--   The Form construction uses the fin poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L481-L490
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L481-L490

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

theorem CircuitLowerBound.Form.fin_polyT {L N c : α → ℕ} {o : α → List ℕ} (hL : PolyT L) (hN : PolyT N) (hc : PolyT c) (ho : PolyT o) :
    PolyT fun x => fin (L x) (N x) (c x) (o x) := by sorry
