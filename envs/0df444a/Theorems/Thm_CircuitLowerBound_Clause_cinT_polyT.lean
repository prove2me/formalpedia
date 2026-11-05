-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_cinT_polyT
-- name    : CircuitLowerBound.Clause.cinT_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:45:52.351977+00:00
-- url     : https://prove2.me/theorems/89f6751f-73fb-44dc-9dcc-a2daf2541297
-- title:
--   Clause: cin T poly T
-- statement:
--   The Clause construction uses the cin T poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L628-L628
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L628-L628

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

theorem CircuitLowerBound.Clause.cinT_polyT {a i : α → ℕ} (h1 : PolyT a) (h2 : PolyT i) : PolyT fun x => cinT (a x) (i x) := by sorry
