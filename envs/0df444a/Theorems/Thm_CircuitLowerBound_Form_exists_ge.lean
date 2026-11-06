-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_exists_ge
-- name    : CircuitLowerBound.Form.exists_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:54:41.617408+00:00
-- url     : https://prove2.me/theorems/2ffc4651-8e96-4ab3-891b-1283d403ffaf
-- title:
--   Form: exists ge
-- statement:
--   The values of the wires on an input satisfy the equations of the gates.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L126-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L126-L131

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
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form

theorem CircuitLowerBound.Form.exists_ge (n : ℕ) (K : List GateD) (hK : WF n K) (x : List Bool) (hx : x.length = n) :
    ∃ a : ℕ → Bool, GE a n K ∧ (List.range n).map a = x := by sorry
