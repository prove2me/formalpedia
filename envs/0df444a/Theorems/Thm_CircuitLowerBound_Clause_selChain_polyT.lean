-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_selChain_polyT
-- name    : CircuitLowerBound.Clause.selChain_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:53:58.160929+00:00
-- url     : https://prove2.me/theorems/31b0f8fd-7a1d-4c26-b1af-7661723424a3
-- title:
--   Clause: sel Chain poly T
-- statement:
--   The Clause construction uses the sel Chain poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L602-L604
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L602-L604

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

theorem CircuitLowerBound.Clause.selChain_polyT {n bq bt rb k : α → ℕ} (h1 : PolyT n) (h2 : PolyT bq) (h3 : PolyT bt) (h4 : Unary rb) (h5 : PolyT k) :
    PolyT fun x => selChain (n x) (bq x) (bt x) (rb x) (k x) := by sorry
