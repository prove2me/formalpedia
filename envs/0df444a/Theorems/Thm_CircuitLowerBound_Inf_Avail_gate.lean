-- Prove2me | Theorems.Thm_CircuitLowerBound_Inf_Avail_gate
-- name    : CircuitLowerBound.Inf.Avail.gate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:10:05.304327+00:00
-- url     : https://prove2.me/theorems/28e2fe5b-ece3-44fa-8b7a-3ce2ec0c9728
-- title:
--   Avail: gate
-- statement:
--   One more gate.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L59-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L59-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Inf
open ENP

theorem CircuitLowerBound.Inf.Avail.gate {n : ℕ} {C : Circuit} {g₁ g₂ : List Bool → Bool} (h₁ : Avail n C g₁) (h₂ : Avail n C g₂) (op : Bool → Bool → Bool) :
    ∃ G : Gate, Avail n (C ++ [G]) fun x => op (g₁ x) (g₂ x) := by sorry
