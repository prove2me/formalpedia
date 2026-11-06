-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_check_out
-- name    : CircuitLowerBound.Form.check_out
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:58:12.212195+00:00
-- url     : https://prove2.me/theorems/5e3102de-05af-4315-8416-93f59848c4ba
-- title:
--   Form: check out
-- statement:
--   What the last wire of the check circuit says, if the equations of all gates hold: each of the
--   three copies of C, on the input that the output wires of G carry, differs from the sign wire.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L287-L316
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L287-L316

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

theorem CircuitLowerBound.Form.check_out (a : ℕ → Bool) {n L : ℕ} {G : List GateD} {o : List ℕ} {C : List GateD} (hL : 1 ≤ L) (hG : WF n G) (hC : WF L C)
    (ho : ∀ i, o.getD i 0 < n + G.length) (hE : GE a n (check L (n + G.length) G o C)) :
    a (n + G.length + C.length + C.length + C.length + 4) = true ↔
      ∀ off ∈ [0, L + 1, L + 1 + (L + 1)],
        eval (toC C) ((List.range L).map fun k => (wires ((List.range n).map a) (toC G)).getD (o.getD (off + k) 0) false) ≠
          (wires ((List.range n).map a) (toC G)).getD (o.getD (off + L) 0) false := by sorry
