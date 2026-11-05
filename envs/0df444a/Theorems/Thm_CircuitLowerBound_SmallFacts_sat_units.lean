-- Prove2me | Theorems.Thm_CircuitLowerBound_SmallFacts_sat_units
-- name    : CircuitLowerBound.SmallFacts.sat_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:54:51.675348+00:00
-- url     : https://prove2.me/theorems/4fb59f84-8fb7-4bf8-bbb4-34cc7bccf65f
-- title:
--   Small Facts: sat units
-- statement:
--   The Small Facts construction uses the sat units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L59-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L59-L60

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

theorem CircuitLowerBound.SmallFacts.sat_units {w : List Bool} {a : ℕ → Bool} : (∀ C ∈ units w, ∃ l ∈ C, a l.1 = l.2) ↔ ∀ i < w.length, a i = w.getD i false := by sorry
