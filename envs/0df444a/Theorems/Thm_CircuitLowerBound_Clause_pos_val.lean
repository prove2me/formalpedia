-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_pos_val
-- name    : CircuitLowerBound.Clause.pos_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:53:11.008126+00:00
-- url     : https://prove2.me/theorems/562ae109-b5b9-47d2-9234-e96c756d7598
-- title:
--   Clause: pos val
-- statement:
--   The output wires for the position carry the position of the literal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L253-L294
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L253-L294

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_Groundwork_PolyT_testBit
attribute [local fun_prop] Groundwork.PolyT.testBit


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks

theorem CircuitLowerBound.Clause.pos_val {v : ℕ → Bool} {z bq P b p0 p1 : ℕ} {dW : ℕ → ℕ} (h : Obeys v b (posG z bq P b p0 p1 dW)) {md q dq : ℕ} (hz : v z = false)
    (hp0 : v p0 = md.testBit 0) (hp1 : v p1 = md.testBit 1) (hq : ∀ i < bq, v i = q.testBit i) (hql : q < 2 ^ bq)
    (hd : ∀ i < bq + 1, v (dW i) = dq.testBit i) :
    num (fun i => v (b + 1 + 7 * i + 3)) (bq + 1) = (qval P q md + dq) % 2 ^ (bq + 1) := by sorry
