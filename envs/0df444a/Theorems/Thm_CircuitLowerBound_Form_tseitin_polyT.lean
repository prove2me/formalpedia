-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_tseitin_polyT
-- name    : CircuitLowerBound.Form.tseitin_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:00:19.690246+00:00
-- url     : https://prove2.me/theorems/4a029f62-7951-483c-91cf-edaf14ea0838
-- title:
--   Form: tseitin poly T
-- statement:
--   The Form construction uses the tseitin poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L498-L500
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L498-L500

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

theorem CircuitLowerBound.Form.tseitin_polyT {n : α → ℕ} {K : α → List GateD} (hn : PolyT n) (hK : PolyT K) : PolyT fun x => tseitin (n x) (K x) := by sorry
