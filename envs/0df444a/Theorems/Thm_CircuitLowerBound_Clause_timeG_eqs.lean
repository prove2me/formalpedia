-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_timeG_eqs
-- name    : CircuitLowerBound.Clause.timeG_eqs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:07:43.741092+00:00
-- url     : https://prove2.me/theorems/a0881fbe-ccd1-4693-a39f-bdd8c716fc36
-- title:
--   Clause: time G eqs
-- statement:
--   The Clause construction uses the time G eqs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L185-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L185-L201

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks

theorem CircuitLowerBound.Clause.timeG_eqs {v : ℕ → Bool} {bq bt a m0 m1 : ℕ} (h : Obeys v a (timeG bq bt a m0 m1)) :
    v a = (v m0 ^^ v m1) ∧ v (a + 1) = (v m1 && !v m0) ∧ v (a + 2) = (v m0 && v m1) ∧
    (∀ i < bt, v (a + 3 + 3 * i) = (v a && v (bq + i)) ∧ v (a + 3 + 3 * i + 1) = (v (a + 3 + 3 * i) ^^ v (cinT a i)) ∧
      v (a + 3 + 3 * i + 2) = (v (a + 3 + 3 * i) && v (cinT a i))) ∧
    v (a + 3 + 3 * bt) = (v (cinT a bt) || v (a + 2)) := by sorry
