-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_offA_polyT
-- name    : CircuitLowerBound.Clause.offA_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:47:12.566895+00:00
-- url     : https://prove2.me/theorems/ed192284-1bea-4623-8c7d-f266d8e6c906
-- title:
--   Clause: off A poly T
-- statement:
--   The Clause construction uses the off A poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L665-L666
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L665-L666

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

theorem CircuitLowerBound.Clause.offA_polyT {n bq bt rb R nf ι : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : PolyT rb) (h5 : PolyT R) (h6 : PolyT nf)
    (h7 : PolyT ι) : PolyT fun x => offA (n x) (bq x) (bt x) (rb x) (R x) (nf x) (ι x) := by sorry
