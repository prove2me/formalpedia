-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_fldChain_polyT
-- name    : CircuitLowerBound.Clause.fldChain_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T21:53:33.58137+00:00
-- url     : https://prove2.me/theorems/9468991f-e7ed-49b2-8b71-8507415d388f
-- title:
--   Clause: fld Chain poly T
-- statement:
--   The Clause construction uses the fld Chain poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L618-L620
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L618-L620

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

theorem CircuitLowerBound.Clause.fldChain_polyT {n rb kbm nf a : α → ℕ} {tb : α → List TCl} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT kbm) (h4 : PolyT nf)
    (h5 : PolyT tb) (h6 : PolyT a) : PolyT fun x => fldChain (n x) (rb x) (kbm x) (nf x) (tb x) (a x) := by sorry
