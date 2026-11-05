-- Prove2me | Theorems.Thm_CircuitLowerBound_SmallFacts_sat_append
-- name    : CircuitLowerBound.SmallFacts.sat_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:54:43.784595+00:00
-- url     : https://prove2.me/theorems/3b6e808a-06bc-46e1-b7d3-1bc4bb117205
-- title:
--   Small Facts: sat append
-- statement:
--   The Small Facts construction uses the sat append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L56-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L56-L57

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Interfaces
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Small
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork
open CircuitLowerBound.SmallFacts

theorem CircuitLowerBound.SmallFacts.sat_append {φ ψ : Cnf} {a : ℕ → Bool} : (∀ C ∈ φ ++ ψ, ∃ l ∈ C, a l.1 = l.2) ↔ (∀ C ∈ φ, ∃ l ∈ C, a l.1 = l.2) ∧ ∀ C ∈ ψ, ∃ l ∈ C, a l.1 = l.2 := by sorry
