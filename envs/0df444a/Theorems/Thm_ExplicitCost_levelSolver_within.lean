-- Prove2me | Theorems.Thm_ExplicitCost_levelSolver_within
-- name    : ExplicitCost.levelSolver_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:08:01.87024+00:00
-- url     : https://prove2.me/theorems/0aaf266c-24e0-4c48-9403-ff8439d6ac80
-- title:
--   Explicit Cost: level Solver within
-- statement:
--   **All stages.** The oracle answers the question for 𝓘 by the list I, that for d by d, those for
--   c^row_i and c^col_i by the numbers of the lists c₀ and c₁, each at the price t; the numbers K and g
--   are written by the loop on states of size at most S₁; and the last stage, on what has been computed,
--   costs T₆ on states of size at most S₆.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L142-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L142-L162

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}

theorem ExplicitCost.levelSolver_within {c x₀ : ℕ} {O : SolQuery → Option Ans} {w : SolQuery → ℕ} {h : Head} {l S₁ : ℕ} {nums : List Unit × List Unit} (hN : (numbersM x₀).Runs h.1.tail (2 * l) S₁ nums) (I : List ℤ) (d : ℤ) (c₀ c₁ : List ℕ) (t : ℕ)
    (hI : O (Sum.inr (Sum.inr (h.2.1, .inr (.inl ())))) = some (.inr I)) (hd : O (Sum.inr (Sum.inr (h.2.1, .inl ()))) = some (.inl d)) (hl₀ : c₀.length = I.length) (hl₁ : c₁.length = I.length)
    (h₀ : ∀ j < I.length, O (Sum.inr (Sum.inr (h.2.1, .inr (.inr (.inl (false, I.getD j 0)))))) = some (.inl (c₀.getD j 0 : ℤ)))
    (h₁ : ∀ j < I.length, O (Sum.inr (Sum.inr (h.2.1, .inr (.inr (.inl (true, I.getD j 0)))))) = some (.inl (c₁.getD j 0 : ℤ)))
    (hw : ∀ q, w (Sum.inr (Sum.inr (h.2.1, q))) = t) {T₆ S₆ : ℕ} {Z : ℤ} (h₆ : (sumAndDivide c).Within O w (((((h, nums), I), d), c₀), c₁) T₆ S₆ Z) :
    (levelSolver c x₀).Within O w h (2 * l + 5 + 2 * I.length + (2 * I.length + 2) * t + T₆) (S₁ + 8 * size (((((h, nums), I), d), c₀), c₁) + S₆ + 10) Z := by sorry
