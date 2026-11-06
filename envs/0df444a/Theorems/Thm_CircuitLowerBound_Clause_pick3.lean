-- Prove2me | Theorems.Thm_CircuitLowerBound_Clause_pick3
-- name    : CircuitLowerBound.Clause.pick3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:56:05.397343+00:00
-- url     : https://prove2.me/theorems/2c83dc00-ae82-4214-8598-98ab98896f05
-- title:
--   Clause: pick3
-- statement:
--   The Clause construction uses the pick3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L767-L776
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Circ/Clause.lean#L767-L776

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Circ_Blocks
import Definitions.Def_ToTuring_Poly_Sat
import Definitions.Def_ToTuring_Poly_Words
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Circ_Clause
import Theorems.Thm_Groundwork_PolyT_flatMap
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.flatMap
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Clause
open ENP Groundwork CircuitLowerBound.Blocks

theorem CircuitLowerBound.Clause.pick3 (f : ℕ → List ℕ) {k : ℕ} (hf : ∀ i, (f i).length = k) {i : ℕ} (hi : i < 3) :
    ∃ rest, ((List.range 3).flatMap f).drop (i * k) = f i ++ rest := by sorry
