-- Prove2me | Theorems.Thm_ExplicitCost_sumRange_poly
-- name    : ExplicitCost.sumRange_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:45:24.929203+00:00
-- url     : https://prove2.me/theorems/22fdb1f3-e06c-4c06-92bb-a9a6bdb4f4f3
-- title:
--   Explicit Cost: sum Range poly
-- statement:
--   The sum over a range.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L83-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L83-L85

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

theorem ExplicitCost.sumRange_poly [HasSize α] [Carried α] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) ℤ} (hN : PolyT N) (hM : M.PolyTimeSteps) : (QueryMachine.sumRange N M).PolyTimeSteps := by sorry
