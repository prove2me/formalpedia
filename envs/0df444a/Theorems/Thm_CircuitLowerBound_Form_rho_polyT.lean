-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_rho_polyT
-- name    : CircuitLowerBound.Form.rho_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T19:50:49.496366+00:00
-- url     : https://prove2.me/theorems/8cecd0aa-07a5-412a-a0b2-48f0f5fe22c5
-- title:
--   Form: rho poly T
-- statement:
--   The Form construction uses the rho poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L471-L474
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L471-L474

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

theorem CircuitLowerBound.Form.rho_polyT {L N off k : α → ℕ} {o : α → List ℕ} (hL : PolyT L) (hN : PolyT N) (ho : PolyT o) (hoff : PolyT off) (hk : PolyT k) :
    PolyT fun x => rho (L x) (N x) (o x) (off x) (k x) := by sorry
