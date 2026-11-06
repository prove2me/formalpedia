-- Prove2me | Theorems.Thm_ExplicitCost_branch_poly
-- name    : ExplicitCost.branch_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:17:07.658479+00:00
-- url     : https://prove2.me/theorems/a7ea0ff9-ee48-420d-a4fe-1a787b6ee50f
-- title:
--   Explicit Cost: branch poly
-- statement:
--   A choice between two machines by a polynomial-time function of the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L61-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L61-L65

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

theorem ExplicitCost.branch_poly {sel : α → α₁ ⊕ α₂} (hs : PolyT sel) {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} (h₁ : M₁.PolyTimeSteps) (h₂ : M₂.PolyTimeSteps) :
    (QueryMachine.branch sel M₁ M₂).PolyTimeSteps := by sorry
