-- Prove2me | Theorems.Thm_ExplicitCost_lamAt_of_lt
-- name    : ExplicitCost.lamAt_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:13:55.030247+00:00
-- url     : https://prove2.me/theorems/bc0ef61a-fb20-4f9b-9beb-6681153c0a74
-- title:
--   Explicit Cost: lam At of lt
-- statement:
--   Λ_j from Λ_{j+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L36-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L36-L43

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

theorem ExplicitCost.lamAt_of_lt (ρ : ℝ) (c x₀ lam B : ℕ) (h : j < l) : lamAt ρ c x₀ l lam B j =
    ⌊((ρ + 3 * zeta j) * ((g x₀ j : ℝ) ^ 4 * lamAt ρ c x₀ l lam B (j + 1)) + (c : ℝ) / 4 * (g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * lamAt ρ c x₀ l lam B (j + 1)) + (K x₀ j : ℝ) ^ 2) / (K x₀ j : ℝ) ^ 2⌋₊ := by sorry
