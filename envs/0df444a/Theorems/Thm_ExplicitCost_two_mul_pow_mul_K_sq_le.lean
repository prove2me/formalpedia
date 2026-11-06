-- Prove2me | Theorems.Thm_ExplicitCost_two_mul_pow_mul_K_sq_le
-- name    : ExplicitCost.two_mul_pow_mul_K_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:11:00.722815+00:00
-- url     : https://prove2.me/theorems/dee81cc2-ecfa-4ee7-ac0f-670507129be9
-- title:
--   Explicit Cost: two mul pow mul K sq le
-- statement:
--   2^{x₀}K² ≤ g⁴/2, for x₀ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L46-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L46-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen

theorem ExplicitCost.two_mul_pow_mul_K_sq_le {x₀ : ℕ} (hx : 1 ≤ x₀) (j : ℕ) : 2 * (2 ^ x₀ * K x₀ j ^ 2) ≤ g x₀ j ^ 4 := by sorry
