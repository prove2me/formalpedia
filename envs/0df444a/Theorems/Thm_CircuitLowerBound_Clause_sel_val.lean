-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_sel_val
-- name    : CircuitLowerBound.Clause.sel_val
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:51:12.910003+00:00
-- url     : https://prove2.me/theorems/986a214c-4531-4046-b918-48820b246e49
-- title:
--   Clause: sel val
-- statement:
--   The wire «r = k».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L299-L315
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L299-L315

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

theorem CircuitLowerBound.Clause.sel_val {v : ℕ → Bool} {n bq bt rb R : ℕ} (h : Obeys v (n + 2) (selG n bq bt rb R)) (hO : v (n + 1) = true) {r : ℕ}
    (hr : ∀ i < rb, v (bq + bt + i) = r.testBit i) (hrl : r < 2 ^ rb) {k : ℕ} (hk : k < R) (hkl : k < 2 ^ rb) : v (Ew n rb k) = decide (r = k) := by sorry
