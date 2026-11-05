-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_length_gatesC
-- name    : CircuitLowerBound.Clause.length_gatesC
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:07:35.722409+00:00
-- url     : https://prove2.me/theorems/29466941-234f-46f1-8f07-01809770c3ee
-- title:
--   Clause: length gates C
-- statement:
--   The Clause construction uses the length gates C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L161-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L161-L164

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

theorem CircuitLowerBound.Clause.length_gatesC (n bq bt rb kbm Dq P : ℕ) (tb : List TCl) :
    (gatesC n bq bt rb kbm Dq P tb).length = 2 + rb * tb.length + tb.length * (3 * (5 + kbm + Dq)) + szL bq bt * 3 := by sorry
