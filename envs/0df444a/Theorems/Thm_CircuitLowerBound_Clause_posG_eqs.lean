-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_posG_eqs
-- name    : CircuitLowerBound.Clause.posG_eqs
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:08:46.526797+00:00
-- url     : https://prove2.me/theorems/df891273-c992-46bf-8407-5194a9321f42
-- title:
--   Clause: pos G eqs
-- statement:
--   The Clause construction uses the pos G eqs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L235-L250
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L235-L250

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

theorem CircuitLowerBound.Clause.posG_eqs {v : ℕ → Bool} {z bq P b p0 p1 : ℕ} {dW : ℕ → ℕ} (h : Obeys v b (posG z bq P b p0 p1 dW)) :
    v b = (v p0 && !v p1) ∧ ∀ i < bq + 1,
      v (b + 1 + 7 * i) = (v b && v (if i < bq then i else z)) ∧
      v (b + 1 + 7 * i + 1) = (if P.testBit i then (v (b + 1 + 7 * i) || v p1) else v (b + 1 + 7 * i)) ∧
      v (b + 1 + 7 * i + 2) = (v (b + 1 + 7 * i + 1) ^^ v (dW i)) ∧
      v (b + 1 + 7 * i + 3) = (v (b + 1 + 7 * i + 2) ^^ v (cinQ z b i)) ∧
      v (b + 1 + 7 * i + 4) = (v (b + 1 + 7 * i + 1) && v (dW i)) ∧
      v (b + 1 + 7 * i + 5) = (v (b + 1 + 7 * i + 2) && v (cinQ z b i)) ∧
      v (b + 1 + 7 * i + 6) = (v (b + 1 + 7 * i + 4) || v (b + 1 + 7 * i + 5)) := by sorry
