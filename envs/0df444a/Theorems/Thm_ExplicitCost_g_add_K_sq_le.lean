-- Prove2me | Theorems.Thm_ExplicitCost_g_add_K_sq_le
-- name    : ExplicitCost.g_add_K_sq_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:16:46.944167+00:00
-- url     : https://prove2.me/theorems/8235640a-90f2-4f24-afde-fbd2dd3cbc45
-- title:
--   Explicit Cost: g add K sq le
-- statement:
--   g + K² ≤ g⁴, for x₀ ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L63-L71
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L63-L71

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

theorem ExplicitCost.g_add_K_sq_le {x₀ : ℕ} (hx : 1 ≤ x₀) (j : ℕ) : g x₀ j + K x₀ j ^ 2 ≤ g x₀ j ^ 4 := by sorry
