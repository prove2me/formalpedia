-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_kb_polyT
-- name    : CircuitLowerBound.Clause.kb_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:47:49.81282+00:00
-- url     : https://prove2.me/theorems/f862e63b-1c44-4473-a3fa-b479f1b0151f
-- title:
--   Clause: kb poly T
-- statement:
--   The Clause construction uses the kb poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L728-L728
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L728-L728

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

theorem CircuitLowerBound.Clause.kb_polyT {e : α → MCode} (h : PolyT e) : PolyT fun x => kb (e x) := by sorry
