-- Prove2me | Theorems.Thm_ExplicitCost_four_mul_le_xiAt
-- name    : ExplicitCost.four_mul_le_xiAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:18:49.55526+00:00
-- url     : https://prove2.me/theorems/a8f8dca3-3903-4335-aedc-54b56362f8b4
-- title:
--   Explicit Cost: four mul le xi At
-- statement:
--   4·Λ_{j+1} ≤ Ξ and 4 ≤ Ξ, for x₀ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L43-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L43-L49

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

theorem ExplicitCost.four_mul_le_xiAt (hx : 1 ≤ x₀) (ρ : ℝ) (c l lam B j : ℕ) (hB : 1 ≤ bitsAt ρ c x₀ l lam B (j + 1)) : 4 * lamAt ρ c x₀ l lam B (j + 1) + 4 ≤ xiAt ρ c x₀ l lam B j := by sorry
