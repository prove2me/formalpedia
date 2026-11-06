-- Prove2me | Theorems.Thm_CircuitLowerBound_Inf_Ext_op
-- name    : CircuitLowerBound.Inf.Ext.op
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:09:22.702619+00:00
-- url     : https://prove2.me/theorems/45f04f12-4bae-4a56-8a56-dd0dfcb48e5c
-- title:
--   Ext: op
-- statement:
--   The Ext construction uses the op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L74-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L74-L78

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

theorem CircuitLowerBound.Inf.Ext.op {n : ℕ} {g₁ g₂ : List Bool → Bool} (h₁ : Ext n g₁) (h₂ : Ext n g₂) (gateFn : Bool → Bool → Bool) : Ext n fun x => gateFn (g₁ x) (g₂ x) := by sorry
