-- Prove2me | Theorems.Thm_ExplicitCost_lift_poly
-- name    : ExplicitCost.lift_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:44:35.505699+00:00
-- url     : https://prove2.me/theorems/3b626d05-7347-4f74-9b09-1f483f03624e
-- title:
--   Explicit Cost: lift poly
-- statement:
--   A step machine with polynomial-time steps, seen as a machine that asks nothing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L28-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L28-L30

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

theorem ExplicitCost.lift_poly {R : Stepped α β} (h : Nonempty (IsPolyT R)) : (QueryMachine.lift R : QueryMachine Q A α β).PolyTimeSteps := by sorry
