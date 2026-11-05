-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_wf_check
-- name    : CircuitLowerBound.Form.wf_check
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:54:06.000498+00:00
-- url     : https://prove2.me/theorems/9d9dce20-4fd3-4acf-b2e1-c31f615e42f9
-- title:
--   Form: wf check
-- statement:
--   In the check circuit every gate reads inputs and earlier gates only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L250-L264
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L250-L264

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

theorem CircuitLowerBound.Form.wf_check {n L : ℕ} {G : List GateD} {o : List ℕ} {C : List GateD} (hL : 1 ≤ L) (hG : WF n G) (hC : WF L C)
    (ho : ∀ i, o.getD i 0 < n + G.length) : WF n (check L (n + G.length) G o C) := by sorry
