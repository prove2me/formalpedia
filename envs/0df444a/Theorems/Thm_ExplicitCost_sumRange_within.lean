-- Prove2me | Theorems.Thm_ExplicitCost_sumRange_within
-- name    : ExplicitCost.sumRange_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:44:11.94868+00:00
-- url     : https://prove2.me/theorems/7f111a67-f85a-451f-8435-444e90704b17
-- title:
--   Explicit Cost: sum Range within
-- statement:
--   Σ_{y < N a} M(a, y); V bounds every |v y|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L112-L126
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L112-L126

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

theorem ExplicitCost.sumRange_within [HasSize α] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) ℤ} {O : Q → Option A} {w : Q → ℕ} {a : α} (T : ℕ → ℕ) (v : ℕ → ℤ) (V Sm : ℕ)
    (hM : ∀ y < N a, M.Within O w (a, y) (T y) Sm (v y)) (hV : ∀ y < N a, (v y).natAbs ≤ V) :
    (QueryMachine.sumRange N M).Within O w a (∑ y ∈ range (N a), (T y + 1)) (size a + size (N a) + (size (N a * V) + Sm) + 1) (∑ y ∈ range (N a), v y) := by sorry
