-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_seg
-- name    : CircuitLowerBound.Form.seg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:11:58.087404+00:00
-- url     : https://prove2.me/theorems/97f3d75d-7793-4929-8573-61a34ff81a03
-- title:
--   Form: seg
-- statement:
--   A copy of the circuit C on L inputs, with the wire k of C moved to the wire ρ k, where the gates
--   go to N, N + 1, …: if the equations of the gates of the copy hold under a, then the wire ρ k carries
--   the value of
--   the wire k of C on the input that the wires ρ 0, …, ρ (L − 1) carry.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L137-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L137-L150

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

theorem CircuitLowerBound.Form.seg (a : ℕ → Bool) (L N : ℕ) (ρ : ℕ → ℕ) (C : List GateD) (hC : WF L C) (hρ : ∀ t, ρ (L + t) = N + t)
    (hE : ∀ t (h : t < C.length), a (N + t) = C[t].toGate.op (a (ρ C[t].2.1)) (a (ρ C[t].2.2))) (k : ℕ) (hk : k < L + C.length) :
    a (ρ k) = (wires ((List.range L).map fun i => a (ρ i)) (toC C)).getD k false := by sorry
