-- Prove2me | Theorems.Thm_ExplicitCost_branch_within_inl
-- name    : ExplicitCost.branch_within_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:45:26.887644+00:00
-- url     : https://prove2.me/theorems/be674ee7-9230-4a78-ac0d-22e4e8f44be8
-- title:
--   Explicit Cost: branch within inl
-- statement:
--   A choice, first machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L63-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L63-L66

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

theorem ExplicitCost.branch_within_inl {sel : α → α₁ ⊕ α₂} {M₁ : QueryMachine Q A α₁ β} {M₂ : QueryMachine Q A α₂ β} {O : Q → Option A} {w : Q → ℕ} {a : α} {x : α₁} {T S : ℕ} {b : β} (hs : sel a = .inl x)
    (h : M₁.Within O w x T S b) : (QueryMachine.branch sel M₁ M₂).Within O w a T (S + 1) b := by sorry
