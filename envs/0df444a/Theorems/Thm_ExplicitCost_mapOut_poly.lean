-- Prove2me | Theorems.Thm_ExplicitCost_mapOut_poly
-- name    : ExplicitCost.mapOut_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:40:52.452193+00:00
-- url     : https://prove2.me/theorems/cf8efc5a-4f2e-4804-9c1e-6d198e4f9b24
-- title:
--   Explicit Cost: map Out poly
-- statement:
--   A polynomial-time function applied to the result.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L50-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L50-L52

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

theorem ExplicitCost.mapOut_poly {M : QueryMachine Q A α β} (hM : M.PolyTimeSteps) {g : β → γ} (hg : PolyT g) : (QueryMachine.mapOut M g).PolyTimeSteps := by sorry
