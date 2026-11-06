-- Prove2me | Theorems.Thm_ExplicitCost_two_mul_c_mul_K_sq_le
-- name    : ExplicitCost.two_mul_c_mul_K_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:07:31.77495+00:00
-- url     : https://prove2.me/theorems/0f81e6ba-18d6-4e42-a51a-52140ccd05e9
-- title:
--   Explicit Cost: two mul c mul K sq le
-- statement:
--   (c + 5)K² ≤ 2^{x₀}K² ≤ g⁴/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L59-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L59-L60

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

theorem ExplicitCost.two_mul_c_mul_K_sq_le {c x₀ : ℕ} (hx : 1 ≤ x₀) (hc : c + 5 ≤ 2 ^ x₀) (j : ℕ) : 2 * ((c + 5) * K x₀ j ^ 2) ≤ g x₀ j ^ 4 := by sorry
