-- Prove2me | Theorems.Thm_ExplicitCost_K_le_g
-- name    : ExplicitCost.K_le_g
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:05:40.166382+00:00
-- url     : https://prove2.me/theorems/364a7f12-30e9-4473-8860-d0a2a5a0f7cc
-- title:
--   Explicit Cost: K le g
-- statement:
--   K_j ≤ g_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L37-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L37-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_Numbers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelNumbers
import Theorems.Thm_ClauseBound_Gen_Pick_K_le_g

set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen

theorem ExplicitCost.K_le_g (x₀ j : ℕ) : K x₀ j ≤ g x₀ j := by sorry
