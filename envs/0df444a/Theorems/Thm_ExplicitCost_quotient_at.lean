-- Prove2me | Theorems.Thm_ExplicitCost_quotient_at
-- name    : ExplicitCost.quotient_at
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:14:04.440166+00:00
-- url     : https://prove2.me/theorems/dbabc845-b417-4160-b52c-8b5aa189b4c5
-- title:
--   Explicit Cost: quotient at
-- statement:
--   The facts on the quotient, for the numbers of the depth j and any Λ ≥ 1 one level up.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L88-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L88-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}

theorem ExplicitCost.quotient_at (hN : Numbers ρ c x₀ lam B) (j : ℕ) {Λ : ℕ} (hΛ : 1 ≤ Λ) :
    1 ≤ ((ρ + 3 * zeta j) * ((g x₀ j : ℝ) ^ 4 * Λ) + (c : ℝ) / 4 * (g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * Λ) + (K x₀ j : ℝ) ^ 2) / (K x₀ j : ℝ) ^ 2 ∧
    ((ρ + 3 * zeta j) * ((g x₀ j : ℝ) ^ 4 * Λ) + (c : ℝ) / 4 * (g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * Λ) + (K x₀ j : ℝ) ^ 2) / (K x₀ j : ℝ) ^ 2 ≤ (g x₀ j : ℝ) ^ 4 * Λ + 1 := by sorry
