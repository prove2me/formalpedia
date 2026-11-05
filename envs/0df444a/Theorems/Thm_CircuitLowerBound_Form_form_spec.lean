-- Prove2me | Theorems.Thm_CircuitLowerBound_Form_form_spec
-- name    : CircuitLowerBound.Form.form_spec
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:58:56.5389+00:00
-- url     : https://prove2.me/theorems/f6f49ff1-9c10-4f06-b0c0-a38bc7da49b2
-- title:
--   Form: form spec
-- statement:
--   The properties of the formula, for a circuit G with output wires o that computes the clauses of
--   the formula of the table e.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L360-L439
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Form.lean#L360-L439

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
import Theorems.Thm_Groundwork_PolyT_dedup
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.dedup
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.Form

theorem CircuitLowerBound.Form.form_spec {e : MCode} {L P : ℕ} (hFit : Fits e L P) {G : List GateD} {o : List ℕ} {C : List GateD} (hG : WF (nb e L) G)
    (ho : o.length = 3 * (L + 1)) (hoN : ∀ w ∈ o, w < nb e L + G.length)
    (hval : ∀ j < 2 ^ nb e L, ∀ i < 3,
      (ofWord (((o.drop (i * (L + 1))).take L).map fun w => (wires (toWord (nb e L) j) (toC G)).getD w false),
        (wires (toWord (nb e L) j) (toC G)).getD (o.getD (i * (L + 1) + L) 0) false) = (clauseAt e L P j).getD i (0, false))
    (hC : WF L C) :
    Shaped3 (nb e L + (check L (nb e L + G.length) G o C).length)
        (tseitin (nb e L) (check L (nb e L + G.length) G o C) ++ [[(nb e L + (check L (nb e L + G.length) G o C).length - 1, true)]]).dedup ∧
      (Sat (tseitin (nb e L) (check L (nb e L + G.length) G o C) ++ [[(nb e L + (check L (nb e L + G.length) G o C).length - 1, true)]]).dedup ↔
        ¬∀ D ∈ tabF e L P, ∃ l ∈ D, eval (toC C) (toWord L l.1) = l.2) := by sorry
