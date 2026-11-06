-- Prove2me | Theorems.Thm_ExplicitCost_level_le
-- name    : ExplicitCost.level_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:23:11.735957+00:00
-- url     : https://prove2.me/theorems/b5aeecc1-ac3c-4dd7-9321-db7cdb9b712a
-- title:
--   Explicit Cost: level le
-- statement:
--   𝒯 = 2^{eK²L}(K(L + B'))^{C₀K²} ≤ 2^{e(ρ+3ζ)N}·Ξ^{cg⁴/4+K²+(c+5)C₀K²}, at the bounds for λ and B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L58-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L58-L106

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

theorem ExplicitCost.level_le (hL : ChainLabel) (hB : ChainBase) (hE : ChainExponent) (hN : Numbers ρ c x₀ lam B) (hj : j < l) (C₀ : ℕ) :
    levelBound ρ c x₀ C₀ l lam B j ≤
      (2 : ℝ) ^ (e ρ x₀ (j + 1) * (K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1) - 3 * ((K x₀ (j + 1) : ℝ) ^ 2 * lamAt ρ c x₀ l lam B (j + 1)) / K x₀ j) *
        (xiAt ρ c x₀ l lam B j : ℝ) ^ (c * (g x₀ j ^ 4 / 4) + K x₀ j ^ 2 + (c + 5) * C₀ * K x₀ j ^ 2) := by sorry
