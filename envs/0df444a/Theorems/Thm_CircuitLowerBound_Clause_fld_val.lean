-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_fld_val
-- name    : CircuitLowerBound.Clause.fld_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:51:44.386629+00:00
-- url     : https://prove2.me/theorems/99e2b130-ee59-4a62-9a69-ddc124acdb26
-- title:
--   Clause: fld val
-- statement:
--   The wire of a bit of what the table says at the place r.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L327-L349
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L327-L349

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks

theorem CircuitLowerBound.Clause.fld_val {v : ℕ → Bool} {n rb kbm nf : ℕ} {tb : List TCl} (h : Obeys v (n + 2 + rb * tb.length) (fldG n rb kbm nf tb)) (hZ : v n = false) {r : ℕ}
    (hE : ∀ k < tb.length, v (Ew n rb k) = decide (r = k)) {a : ℕ} (ha : a < 3 * nf) :
    v (prevW (n + 2 + rb * tb.length + tb.length * a) n tb.length) = fbit kbm (litI (tb.getD r zeroCl) (a / nf)) (a % nf) := by sorry
