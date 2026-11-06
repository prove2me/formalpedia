-- Prove2me | Theorems.Thm_ExplicitCost_bind_within
-- name    : ExplicitCost.bind_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:44:39.830102+00:00
-- url     : https://prove2.me/theorems/3ad5c5db-fe0e-49f7-816c-4f7a516df274
-- title:
--   Explicit Cost: bind within
-- statement:
--   M, then N: the costs add up, with one more step for the hand-over.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L83-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L83-L87

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

theorem ExplicitCost.bind_within [HasSize α] {M : QueryMachine Q A α β} {N : QueryMachine Q A (α × β) γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T T' S S' : ℕ} {b : β} {c : γ} (h : M.Within O w a T S b)
    (h' : N.Within O w (a, b) T' S' c) : (QueryMachine.bind M N).Within O w a (T + 1 + T') (max (size a + S) S' + 1) c := by sorry
