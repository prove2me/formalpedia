-- Prove2me | Theorems.Thm_ExplicitCost_g_pos
-- name    : ExplicitCost.g_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:07:27.574365+00:00
-- url     : https://prove2.me/theorems/7d99f282-6502-45a4-aa66-dd040fa1adf5
-- title:
--   Explicit Cost: g pos
-- statement:
--   g_j ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L43-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L43-L43

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

theorem ExplicitCost.g_pos (x₀ j : ℕ) : 1 ≤ g x₀ j := by sorry
