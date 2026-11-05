-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_dWire_polyT
-- name    : CircuitLowerBound.Clause.dWire_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:46:23.546198+00:00
-- url     : https://prove2.me/theorems/ec3db4a3-36bc-4d46-8622-2b5e2537fd82
-- title:
--   Clause: d Wire poly T
-- statement:
--   The Clause construction uses the d Wire poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L644-L645
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L644-L645

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

theorem CircuitLowerBound.Clause.dWire_polyT {n rb R kbm Dq ι i : α → ℕ} (h1 : PolyT n) (h2 : PolyT rb) (h3 : PolyT R) (h4 : PolyT kbm) (h5 : PolyT Dq) (h6 : PolyT ι)
    (h7 : PolyT i) : PolyT fun x => dWire (n x) (rb x) (R x) (kbm x) (Dq x) (ι x) (i x) := by sorry
