-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_selGate_polyT
-- name    : CircuitLowerBound.Clause.selGate_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:45:38.715226+00:00
-- url     : https://prove2.me/theorems/d7cddabe-8a4e-4e04-96bd-198ea627e730
-- title:
--   Clause: sel Gate poly T
-- statement:
--   The Clause construction uses the sel Gate poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L599-L600
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L599-L600

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

theorem CircuitLowerBound.Clause.selGate_polyT {n bq bt rb k i : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : PolyT rb) (h5 : PolyT k) (h6 : PolyT i) :
    PolyT fun x => selGate (n x) (bq x) (bt x) (rb x) (k x) (i x) := by sorry
