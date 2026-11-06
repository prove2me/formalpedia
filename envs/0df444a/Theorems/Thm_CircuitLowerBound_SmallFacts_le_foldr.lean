-- Prove2me | Theorems.Thm_CircuitLowerBound_SmallFacts_le_foldr
-- name    : CircuitLowerBound.SmallFacts.le_foldr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:42:33.72588+00:00
-- url     : https://prove2.me/theorems/9d057a43-652e-4c1a-b0f3-a71d7863e5d5
-- title:
--   Small Facts: le foldr
-- statement:
--   The Small Facts construction uses the le foldr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L115-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L115-L120

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

theorem CircuitLowerBound.SmallFacts.le_foldr (j : ℕ) (w : List Bool) : j ≤ (List.replicate j true ++ w).foldr Nat.bit 0 := by sorry
