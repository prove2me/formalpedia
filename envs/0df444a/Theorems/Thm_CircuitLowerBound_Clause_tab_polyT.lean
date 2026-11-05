-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_tab_polyT
-- name    : CircuitLowerBound.Clause.tab_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:47:09.207888+00:00
-- url     : https://prove2.me/theorems/2d552f5f-b0ca-40fd-9afe-75b4fc76d421
-- title:
--   Clause: tab poly T
-- statement:
--   The Clause construction uses the tab poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L732-L732
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L732-L732

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

theorem CircuitLowerBound.Clause.tab_polyT {e : α → MCode} (h : PolyT e) : PolyT fun x => tab (e x) := by sorry
