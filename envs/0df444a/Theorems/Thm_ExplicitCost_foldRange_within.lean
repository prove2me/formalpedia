-- Prove2me | Theorems.Thm_ExplicitCost_foldRange_within
-- name    : ExplicitCost.foldRange_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:44:42.524458+00:00
-- url     : https://prove2.me/theorems/eaa3c312-8b82-4506-9e26-d87535d7be01
-- title:
--   Explicit Cost: fold Range within
-- statement:
--   The loop over y < N a: the costs of the rounds add up, with one more step for each round.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L96-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L96-L109

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

theorem ExplicitCost.foldRange_within [HasSize α] [HasSize γ] {N : α → ℕ} {M : QueryMachine Q A (α × ℕ) β} {g : γ → ℕ → β → γ} {c₀ : α → γ} {O : Q → Option A} {w : Q → ℕ} {a : α} (T : ℕ → ℕ) (v : ℕ → β) (Sc Sm : ℕ)
    (hM : ∀ y < N a, M.Within O w (a, y) (T y) Sm (v y)) (hc : ∀ k ≤ N a, size ((List.range k).foldl (fun c y => g c y (v y)) (c₀ a)) ≤ Sc) :
    (QueryMachine.foldRange N M g c₀).Within O w a (∑ y ∈ range (N a), (T y + 1)) (size a + size (N a) + (Sc + Sm) + 1) ((List.range (N a)).foldl (fun c y => g c y (v y)) (c₀ a)) := by sorry
