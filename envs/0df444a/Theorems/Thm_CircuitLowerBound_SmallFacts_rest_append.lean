-- Prove2me | Theorems.Thm_CircuitLowerBound_SmallFacts_rest_append
-- name    : CircuitLowerBound.SmallFacts.rest_append
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:42:23.774527+00:00
-- url     : https://prove2.me/theorems/f637fb57-a2aa-423c-969d-e41b4b4b1b48
-- title:
--   Small Facts: rest append
-- statement:
--   The Small Facts construction uses the rest append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L99-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L99-L104

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

theorem CircuitLowerBound.SmallFacts.rest_append (j : ℕ) (x : List Bool) : rest (List.replicate j true ++ false :: x) = x := by sorry
