-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_Ew_polyT
-- name    : CircuitLowerBound.Clause.Ew_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:45:10.152298+00:00
-- url     : https://prove2.me/theorems/6d578b3a-6553-488d-8dd3-5a3df00d7a53
-- title:
--   Clause: Ew poly T
-- statement:
--   The Clause construction uses the Ew poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L596-L597
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L596-L597

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
variable {α : Type} [Enc α]

theorem CircuitLowerBound.Clause.Ew_polyT {n rb k : α → ℕ} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT k) : PolyT fun x => Ew (n x) (rb x) (k x) := by sorry
