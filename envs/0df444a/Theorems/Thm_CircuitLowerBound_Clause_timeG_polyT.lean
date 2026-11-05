-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_timeG_polyT
-- name    : CircuitLowerBound.Clause.timeG_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:54:28.924006+00:00
-- url     : https://prove2.me/theorems/991dd50f-d38c-4232-90c4-c126c1d4a4c0
-- title:
--   Clause: time G poly T
-- statement:
--   The Clause construction uses the time G poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L636-L642
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L636-L642

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

theorem CircuitLowerBound.Clause.timeG_polyT {bq bt a m0 m1 : α → ℕ} (h1 : PolyT bq) (h2 : Unary bt) (h3 : PolyT a) (h4 : PolyT m0) (h5 : PolyT m1) :
    PolyT fun x => timeG (bq x) (bt x) (a x) (m0 x) (m1 x) := by sorry
