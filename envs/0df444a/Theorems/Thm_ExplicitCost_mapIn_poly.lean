-- Prove2me | Theorems.Thm_ExplicitCost_mapIn_poly
-- name    : ExplicitCost.mapIn_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:40:20.131762+00:00
-- url     : https://prove2.me/theorems/a92a41c9-a712-4088-aebd-c8e53ce6547a
-- title:
--   Explicit Cost: map In poly
-- statement:
--   A polynomial-time function applied to the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L45-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L45-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyRules
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines QueryMachines.QueryMachine Printed
variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]

theorem ExplicitCost.mapIn_poly {g : α → β} (hg : PolyT g) {M : QueryMachine Q A β γ} (hM : M.PolyTimeSteps) : (QueryMachine.mapIn g M).PolyTimeSteps := by sorry
