-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_size_aux
-- name    : CircuitLowerBound.Clause.size_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:50:12.725448+00:00
-- url     : https://prove2.me/theorems/f38c3fbd-eb90-4541-b040-5116eb0c4c72
-- title:
--   Clause: size aux
-- statement:
--   The Clause construction uses the size aux property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L738-L738
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L738-L738

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

theorem CircuitLowerBound.Clause.size_aux {f : α → ℕ} (h : PolyT f) : PolyT fun x => Nat.size (f x) := by sorry
