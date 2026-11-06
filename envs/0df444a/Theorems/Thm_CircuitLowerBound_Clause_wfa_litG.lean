-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_wfa_litG
-- name    : CircuitLowerBound.Clause.wfa_litG
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:52:28.169552+00:00
-- url     : https://prove2.me/theorems/40798310-039f-4558-9771-05faef18c02e
-- title:
--   Clause: wfa lit G
-- statement:
--   The Clause construction uses the wfa lit G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L420-L430
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L420-L430

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

theorem CircuitLowerBound.Clause.wfa_litG {n bq bt rb : ℕ} (hn : bq + bt + rb ≤ n) (R kbm Dq P : ℕ) {ι : ℕ} (hι : ι < 3) :
    WFa (offA n bq bt rb R (5 + kbm + Dq) ι) (litG n bq bt rb R kbm Dq P ι) := by sorry
