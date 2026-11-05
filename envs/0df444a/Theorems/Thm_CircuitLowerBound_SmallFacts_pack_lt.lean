-- Prove2me | Theorems.Thm_CircuitLowerBound_SmallFacts_pack_lt
-- name    : CircuitLowerBound.SmallFacts.pack_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:42:20.795491+00:00
-- url     : https://prove2.me/theorems/059a8972-d094-41d4-8149-466595e98ab1
-- title:
--   Small Facts: pack lt
-- statement:
--   The Small Facts construction uses the pack lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L39-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L39-L42

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

theorem CircuitLowerBound.SmallFacts.pack_lt {x y A M : ℕ} (hx : x < A) (hy : y < M) : x * M + y < A * M := by sorry
