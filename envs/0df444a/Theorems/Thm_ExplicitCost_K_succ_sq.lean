-- Prove2me | Theorems.Thm_ExplicitCost_K_succ_sq
-- name    : ExplicitCost.K_succ_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:05:35.728379+00:00
-- url     : https://prove2.me/theorems/329cebc3-3bc3-442e-bbb0-0098d970323a
-- title:
--   Explicit Cost: K succ sq
-- statement:
--   K_{j+1}² = g_j⁴.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L27-L27
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L27-L27

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

theorem ExplicitCost.K_succ_sq (x₀ j : ℕ) : K x₀ (j + 1) ^ 2 = g x₀ j ^ 4 := by sorry
