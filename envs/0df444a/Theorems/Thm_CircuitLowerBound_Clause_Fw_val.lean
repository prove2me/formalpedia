-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_Fw_val
-- name    : CircuitLowerBound.Clause.Fw_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:51:31.15258+00:00
-- url     : https://prove2.me/theorems/4c8f4ce7-0f30-4d74-a30a-7ca788991fa2
-- title:
--   Clause: Fw val
-- statement:
--   The wire of bit f of literal ι.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L352-L360
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L352-L360

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

theorem CircuitLowerBound.Clause.Fw_val {v : ℕ → Bool} {n rb kbm nf : ℕ} {tb : List TCl} (h : Obeys v (n + 2 + rb * tb.length) (fldG n rb kbm nf tb)) (hZ : v n = false) {r : ℕ}
    (hE : ∀ k < tb.length, v (Ew n rb k) = decide (r = k)) {ι f : ℕ} (hι : ι < 3) (hf : f < nf) :
    v (Fw n rb tb.length nf ι f) = fbit kbm (litI (tb.getD r zeroCl) ι) f := by sorry
