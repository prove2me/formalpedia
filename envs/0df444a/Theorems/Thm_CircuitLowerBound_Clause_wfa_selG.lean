-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_wfa_selG
-- name    : CircuitLowerBound.Clause.wfa_selG
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:51:51.924604+00:00
-- url     : https://prove2.me/theorems/c6e6dfa5-655b-4ff0-98ca-88d4ebbab706
-- title:
--   Clause: wfa sel G
-- statement:
--   The Clause construction uses the wfa sel G property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L385-L390
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L385-L390

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

theorem CircuitLowerBound.Clause.wfa_selG {n bq bt rb : ℕ} (hn : bq + bt + rb ≤ n) (R : ℕ) : WFa (n + 2) (selG n bq bt rb R) := by sorry
