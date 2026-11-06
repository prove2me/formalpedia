-- Prove2me | Theorems.Thm_ExplicitCost_baseAt_cast
-- name    : ExplicitCost.baseAt_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:18:57.391662+00:00
-- url     : https://prove2.me/theorems/da191e08-2d10-47d9-9752-30979bcba887
-- title:
--   Explicit Cost: base At cast
-- statement:
--   The base of the polynomial factor, as a real number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L37-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L37-L40

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

theorem ExplicitCost.baseAt_cast (ρ : ℝ) (c x₀ l lam B j : ℕ) : (K x₀ j : ℝ) * ((lamAt ρ c x₀ l lam B j : ℝ) + bitsAt ρ c x₀ l lam B j) = (baseAt ρ c x₀ l lam B j : ℝ) := by sorry
