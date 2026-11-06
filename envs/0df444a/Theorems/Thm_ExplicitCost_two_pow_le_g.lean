-- Prove2me | Theorems.Thm_ExplicitCost_two_pow_le_g
-- name    : ExplicitCost.two_pow_le_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:04:10.201897+00:00
-- url     : https://prove2.me/theorems/a9dab89a-d560-459c-b7f4-f3a0aa1fd8fb
-- title:
--   Explicit Cost: two pow le g
-- statement:
--   2^{x₀} ≤ g_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L40-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L40-L40

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

theorem ExplicitCost.two_pow_le_g (x₀ j : ℕ) : 2 ^ x₀ ≤ g x₀ j := by sorry
