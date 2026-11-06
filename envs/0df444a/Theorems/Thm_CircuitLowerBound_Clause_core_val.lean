-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_core_val
-- name    : CircuitLowerBound.Clause.core_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:08:40.672068+00:00
-- url     : https://prove2.me/theorems/fb62a0e4-eec6-4abe-a9fe-eaa3691731e6
-- title:
--   Clause: core val
-- statement:
--   The values of the output wires of literal ι, for the clause number j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L487-L580
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L487-L580

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks

theorem CircuitLowerBound.Clause.core_val {n bq bt rb kbm Dq L P : ℕ} {tb : List TCl} (hn : n = rb + bt + bq) (hbt : 1 ≤ bt) (hR : tb.length < 2 ^ rb) (hL : bq + bt + 2 + kbm ≤ L)
    (hD : ∀ k ι i, Dq ≤ i → i < bq + 1 → (litI (tb.getD k zeroCl) ι).2.2.2.1.testBit i = false) {j : ℕ} (hj : j < 2 ^ n) {ι : ℕ} (hι : ι < 3)
    (v : ℕ → Bool) (hv : v = fun i => (wires (toWord n j) (toC (gatesC n bq bt rb kbm Dq P tb))).getD i false)
    (l : TLit) (hl : l = litI (tb.getD (j / 2 ^ (bt + bq)) zeroCl) ι) :
    ofWord (((outsL n bq bt rb tb.length kbm Dq L ι).take L).map v) =
      ((l.1 % 2 ^ kbm) * 2 ^ (bt + 1) + tval bt (j / 2 ^ bq % 2 ^ bt) l.2.1) * 2 ^ (bq + 1) + (qval P (j % 2 ^ bq) l.2.2.1 + l.2.2.2.1) % 2 ^ (bq + 1) ∧
    v ((outsL n bq bt rb tb.length kbm Dq L ι).getD L 0) = l.2.2.2.2 := by sorry
