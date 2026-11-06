-- Prove2me | Theorems.Thm_ExplicitCost_two_pow_mul_K_le_g
-- name    : ExplicitCost.two_pow_mul_K_le_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:07:20.228191+00:00
-- url     : https://prove2.me/theorems/8a4b0d3a-f717-4058-94dc-15e34353a184
-- title:
--   Explicit Cost: two pow mul K le g
-- statement:
--   2^{x₀}K_j ≤ g_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L33-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L33-L34

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

theorem ExplicitCost.two_pow_mul_K_le_g (x₀ j : ℕ) : 2 ^ x₀ * K x₀ j ≤ g x₀ j := by sorry
