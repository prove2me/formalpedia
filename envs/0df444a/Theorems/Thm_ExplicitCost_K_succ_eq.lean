-- Prove2me | Theorems.Thm_ExplicitCost_K_succ_eq
-- name    : ExplicitCost.K_succ_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:11:09.181756+00:00
-- url     : https://prove2.me/theorems/708d96ef-8c34-413b-8566-3b03d9f5b511
-- title:
--   Explicit Cost: K succ eq
-- statement:
--   K_{j+1} = g_j².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L24-L24
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L24-L24

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

theorem ExplicitCost.K_succ_eq (x₀ j : ℕ) : K x₀ (j + 1) = g x₀ j ^ 2 := by sorry
