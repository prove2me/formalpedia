-- Prove2me | Theorems.Thm_ExplicitCost_branch_within_inr
-- name    : ExplicitCost.branch_within_inr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:44:36.653193+00:00
-- url     : https://prove2.me/theorems/da6be6ec-3fc7-4f3c-b6cb-a30db0f23d1d
-- title:
--   Explicit Cost: branch within inr
-- statement:
--   A choice, second machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L69-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L69-L72

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

theorem ExplicitCost.branch_within_inr {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} {O : Q → Option A} {w : Q → ℕ} {a : α} {y : α₂} {T S : ℕ} {b : β} (hs : sel a = .inr y)
    (h : M₂.Within O w y T S b) : (QueryMachine.branch sel M₁ M₂).Within O w a T (S + 1) b := by sorry
