-- Prove2me | Theorems.Thm_ExplicitCost_bind_poly
-- name    : ExplicitCost.bind_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:42:51.447838+00:00
-- url     : https://prove2.me/theorems/e5b2ef01-451d-4457-997e-8f49391b37cd
-- title:
--   Explicit Cost: bind poly
-- statement:
--   One machine after the other.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L55-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L55-L58

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

theorem ExplicitCost.bind_poly [HasSize α] [Carried α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} (hM : M.PolyTimeSteps) (hN : N.PolyTimeSteps) : (QueryMachine.bind M N).PolyTimeSteps := by sorry
