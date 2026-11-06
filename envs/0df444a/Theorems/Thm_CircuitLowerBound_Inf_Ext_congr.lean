-- Prove2me | Theorems.Thm_CircuitLowerBound_Inf_Ext_congr
-- name    : CircuitLowerBound.Inf.Ext.congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:10:21.117467+00:00
-- url     : https://prove2.me/theorems/3f4d1766-5fb5-4b10-b2a3-f02ff0c9cbaf
-- title:
--   Ext: congr
-- statement:
--   The Ext construction uses the congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L70-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Inf.lean#L70-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBoundInfinitelyOftenStatement
import Definitions.Def_CircuitLowerBound_Closed
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Inf
import Theorems.Thm_Groundwork_PolyT_congr
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Inf
open ENP

theorem CircuitLowerBound.Inf.Ext.congr {n : ℕ} {g g' : List Bool → Bool} (h : Ext n g) (e : ∀ x : List Bool, x.length = n → g x = g' x) : Ext n g' := by sorry
