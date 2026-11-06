-- Prove2me | Theorems.Thm_ExplicitCost_two_add_le_K_sq
-- name    : ExplicitCost.two_add_le_K_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:16:43.45136+00:00
-- url     : https://prove2.me/theorems/75eab3e7-2ddc-442f-8025-25dd93750ba6
-- title:
--   Explicit Cost: two add le K sq
-- statement:
--   2 + c/4 ≤ K_j².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L81-L85
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L81-L85

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_GeneralPieces_DefGenPieces_Conv
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChainLabel
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}

theorem ExplicitCost.two_add_le_K_sq (hc : c + 5 ≤ 2 ^ x₀) (j : ℕ) : 2 + (c : ℝ) / 4 ≤ (K x₀ j : ℝ) ^ 2 := by sorry
