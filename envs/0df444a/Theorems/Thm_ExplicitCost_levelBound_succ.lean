-- Prove2me | Theorems.Thm_ExplicitCost_levelBound_succ
-- name    : ExplicitCost.levelBound_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:19:43.972397+00:00
-- url     : https://prove2.me/theorems/baf3d52f-1a8f-4f37-ad46-47c8135418bd
-- title:
--   Explicit Cost: level Bound succ
-- statement:
--   The bound of the depth j + 1, with Ξ for its base.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L116-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L116-L119

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}

theorem ExplicitCost.levelBound_succ (ρ : ℝ) (c x₀ C₀ l lam B j : ℕ) : levelBound ρ c x₀ C₀ l lam B (j + 1) =
    (2 : ℝ) ^ (e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) * (xiAt ρ c x₀ l lam B j : ℝ) ^ (C₀ * K x₀ (j + 1) ^ 2) := by sorry
