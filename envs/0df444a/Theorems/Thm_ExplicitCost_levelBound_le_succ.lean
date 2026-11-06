-- Prove2me | Theorems.Thm_ExplicitCost_levelBound_le_succ
-- name    : ExplicitCost.levelBound_le_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:22:38.935205+00:00
-- url     : https://prove2.me/theorems/d39b53e7-e9f6-445c-b758-40a318c40a29
-- title:
--   Explicit Cost: level Bound le succ
-- statement:
--   The bound of the depth j is at most that of the depth j + 1, for C₀ ≥ 2(c + 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L122-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L122-L139

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

theorem ExplicitCost.levelBound_le_succ (hL : ChainLabel) (hBl : BoundBelow) (hEF : ExponentFits) (hN : Numbers ρ c x₀ lam B) (hj : j < l) {C₀ : ℕ} (hC : 2 * (c + 1) ≤ C₀) :
    levelBound ρ c x₀ C₀ l lam B j ≤ levelBound ρ c x₀ C₀ l lam B (j + 1) := by sorry
