-- Prove2me | Theorems.Thm_ExplicitCost_two_pow_le_K
-- name    : ExplicitCost.two_pow_le_K
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:06:36.184337+00:00
-- url     : https://prove2.me/theorems/4d81f913-45bd-4e3d-adc6-348a30850749
-- title:
--   Explicit Cost: two pow le K
-- statement:
--   2^{x₀} ≤ K_j.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L30-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelNumbers.lean#L30-L30

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

theorem ExplicitCost.two_pow_le_K (x₀ j : ℕ) : 2 ^ x₀ ≤ K x₀ j := by sorry
