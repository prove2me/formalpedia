-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_wfa_gatesC
-- name    : CircuitLowerBound.Clause.wfa_gatesC
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:49:15.917138+00:00
-- url     : https://prove2.me/theorems/296f79f8-ceba-4139-b7cc-0fd73027d09d
-- title:
--   Clause: wfa gates C
-- statement:
--   The Clause construction uses the wfa gates C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L432-L449
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L432-L449

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

theorem CircuitLowerBound.Clause.wfa_gatesC {n bq bt rb : ℕ} (hn : bq + bt + rb ≤ n) (h1 : 1 ≤ n) (kbm Dq P : ℕ) (tb : List TCl) : WFa n (gatesC n bq bt rb kbm Dq P tb) := by sorry
