-- Prove2me | Theorems.Thm_ExplicitCost_one_le_lamAt
-- name    : ExplicitCost.one_le_lamAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:13:02.781993+00:00
-- url     : https://prove2.me/theorems/db418034-5180-4022-b6b6-d3feb50fad20
-- title:
--   Explicit Cost: one le lam At
-- statement:
--   Λ_j ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L109-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L109-L109

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

theorem ExplicitCost.one_le_lamAt (hN : Numbers ρ c x₀ lam B) (hj : j ≤ l) : 1 ≤ lamAt ρ c x₀ l lam B j := by sorry
