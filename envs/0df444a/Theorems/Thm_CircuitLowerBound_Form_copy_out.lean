-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_copy_out
-- name    : CircuitLowerBound.Form.copy_out
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:54:55.673054+00:00
-- url     : https://prove2.me/theorems/501b1c26-b94a-4b69-ab5e-bed6cb82fec5
-- title:
--   Form: copy out
-- statement:
--   The output wire of a copy carries the output of the circuit on the input that the wires named by
--   o carry.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L268-L277
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L268-L277

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

theorem CircuitLowerBound.Form.copy_out (a : ℕ → Bool) {L N : ℕ} (o : List ℕ) (off : ℕ) {C : List GateD} (hL : 1 ≤ L) (hC : WF L C) (hE : GE a N (reloc L N o off C)) :
    a (rho L N o off (L + C.length - 1)) = eval (toC C) ((List.range L).map fun k => a (o.getD (off + k) 0)) := by sorry
