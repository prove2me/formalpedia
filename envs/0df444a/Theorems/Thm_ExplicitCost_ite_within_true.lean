-- Prove2me | Theorems.Thm_ExplicitCost_ite_within_true
-- name    : ExplicitCost.ite_within_true
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:41:10.124315+00:00
-- url     : https://prove2.me/theorems/5cb2d701-ec42-449d-b9b9-a3f5d62bcf1d
-- title:
--   Explicit Cost: ite within true
-- statement:
--   M if p a.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L75-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L75-L76

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

theorem ExplicitCost.ite_within_true {p : α → Bool} {M N : QueryMachine Q A α β} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {b : β} (hp : p a = true) (h : M.Within O w a T S b) :
    (QueryMachine.ite p M N).Within O w a T (S + 1) b := by sorry
