-- Prove2me | Theorems.Thm_ExplicitCost_four_mul_div_g
-- name    : ExplicitCost.four_mul_div_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:19:09.9312+00:00
-- url     : https://prove2.me/theorems/8987a967-50be-456c-909c-ee1c9f39b677
-- title:
--   Explicit Cost: four mul div g
-- statement:
--   4 divides g⁴, for x₀ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L52-L55
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L52-L55

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

theorem ExplicitCost.four_mul_div_g (hx : 1 ≤ x₀) (j : ℕ) : 4 * (g x₀ j ^ 4 / 4) = g x₀ j ^ 4 := by sorry
