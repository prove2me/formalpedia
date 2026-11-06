-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_outs_aux2
-- name    : CircuitLowerBound.Clause.outs_aux2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:55:37.972985+00:00
-- url     : https://prove2.me/theorems/3ca73120-5ce2-4fa2-a9b5-799a65718cf4
-- title:
--   Clause: outs aux2
-- statement:
--   The Clause construction uses the outs aux2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L695-L696
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L695-L696

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks
variable {α : Type} [Enc α]

theorem CircuitLowerBound.Clause.outs_aux2 {a w : α → ℕ} (h1 : PolyT a) (h3 : Unary w) : PolyT fun x => (List.range (w x)).map fun i => a x + 3 + 3 * i + 1 := by sorry
