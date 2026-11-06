-- Prove2me | Theorems.Thm_ExplicitCost_levelBound_le_top
-- name    : ExplicitCost.levelBound_le_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:23:15.017695+00:00
-- url     : https://prove2.me/theorems/9e8e8899-b68f-494d-ab02-1975c9410d0a
-- title:
--   Explicit Cost: level Bound le top
-- statement:
--   So the bound of every depth j ≤ ℓ is at most the bound of the theorem for the outermost
--   instance.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L143-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L143-L154

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

theorem ExplicitCost.levelBound_le_top (hL : ChainLabel) (hBl : BoundBelow) (hEF : ExponentFits) (hN : Numbers ρ c x₀ lam B) {C₀ : ℕ} (hC : 2 * (c + 1) ≤ C₀) (l : ℕ) :
    ∀ k j, j + k = l → levelBound ρ c x₀ C₀ l lam B j ≤ timeBound ρ x₀ C₀ l lam B := by sorry
