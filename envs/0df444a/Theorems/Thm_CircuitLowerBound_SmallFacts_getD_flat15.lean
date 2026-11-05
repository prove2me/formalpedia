-- Prove2me | Theorems.Thm_CircuitLowerBound_SmallFacts_getD_flat15
-- name    : CircuitLowerBound.SmallFacts.getD_flat15
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:42:35.10212+00:00
-- url     : https://prove2.me/theorems/4712f311-bd69-417d-beda-27f2a80833cf
-- title:
--   Small Facts: get D flat15
-- statement:
--   Entry 15·r + i of the numbers of a list of clauses.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L150-L158
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Small.lean#L150-L158

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

theorem CircuitLowerBound.SmallFacts.getD_flat15 : ∀ (X : List TCl) (r i : ℕ), r < X.length → i < 15 → ((X.map n15).flatten).getD (15 * r + i) 0 = (n15 (X.getD r zeroCl)).getD i 0
  := by sorry
