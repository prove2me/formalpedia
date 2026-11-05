-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_fbit_polyT
-- name    : CircuitLowerBound.Clause.fbit_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:45:21.965962+00:00
-- url     : https://prove2.me/theorems/8cf09e39-7d7e-4dab-9656-7edd35ba49c2
-- title:
--   Clause: fbit poly T
-- statement:
--   The Clause construction uses the fbit poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L593-L594
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L593-L594

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

theorem CircuitLowerBound.Clause.fbit_polyT {kbm f : α → ℕ} {l : α → TLit} (h1 : PolyT kbm) (h2 : PolyT l) (h3 : PolyT f) :
    PolyT fun x => fbit (kbm x) (l x) (f x) := by sorry
