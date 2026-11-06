-- Prove2me | Theorems.Thm_ExplicitCost_lift_within
-- name    : ExplicitCost.lift_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:42:11.008487+00:00
-- url     : https://prove2.me/theorems/53ac2830-d1dc-4771-8165-6c5fe5358d0c
-- title:
--   Explicit Cost: lift within
-- statement:
--   A step machine asks nothing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L32-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L32-L33

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Within
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}

theorem ExplicitCost.lift_within {R : Stepped α β} {O : Q → Option A} {w : Q → ℕ} {a : α} {t S : ℕ} {b : β} (h : R.Runs a t S b) : (QueryMachine.lift R : QueryMachine Q A α β).Within O w a t S b := by sorry
