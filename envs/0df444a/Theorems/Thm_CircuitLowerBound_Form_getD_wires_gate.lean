-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_getD_wires_gate
-- name    : CircuitLowerBound.Form.getD_wires_gate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:11:01.171414+00:00
-- url     : https://prove2.me/theorems/f44c3425-e49d-4ea0-acd1-d48ea867a606
-- title:
--   Form: get D wires gate
-- statement:
--   The wire of a gate carries the value of the gate on the wires that it reads.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L88-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L88-L111

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
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form

theorem CircuitLowerBound.Form.getD_wires_gate (C : List GateD) (w : List Bool) (hC : WF w.length C) (t : ℕ) (h : t < C.length) :
    (wires w (toC C)).getD (w.length + t) false
      = C[t].toGate.op ((wires w (toC C)).getD C[t].2.1 false) ((wires w (toC C)).getD C[t].2.2 false) := by sorry
