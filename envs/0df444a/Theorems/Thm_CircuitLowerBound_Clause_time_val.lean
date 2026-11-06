-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_time_val
-- name    : CircuitLowerBound.Clause.time_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:08:13.887832+00:00
-- url     : https://prove2.me/theorems/3b0114c6-1972-4bd0-b53b-23364c1f210a
-- title:
--   Clause: time val
-- statement:
--   The output wires for the time carry the time of the literal.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L204-L231
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L204-L231

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

theorem CircuitLowerBound.Clause.time_val {v : ℕ → Bool} {bq bt a m0 m1 : ℕ} (h : Obeys v a (timeG bq bt a m0 m1)) {md t : ℕ} (hm0 : v m0 = md.testBit 0)
    (hm1 : v m1 = md.testBit 1) (ht : ∀ i < bt, v (bq + i) = t.testBit i) (htl : t < 2 ^ bt) :
    num (fun i => v (a + 3 + 3 * i + 1)) bt + 2 ^ bt * (v (a + 3 + 3 * bt)).toNat = tval bt t md := by sorry
