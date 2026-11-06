-- Prove2me | Theorems.Thm_ExplicitCost_lamAt_pos
-- name    : ExplicitCost.lamAt_pos
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:19:42.215965+00:00
-- url     : https://prove2.me/theorems/d6e0c104-4d96-42f0-bd8c-7a3a86a1dfe8
-- title:
--   Explicit Cost: lam At pos
-- statement:
--   1 ≤ Λ_j for every j ≤ ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L95-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L95-L106

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

theorem ExplicitCost.lamAt_pos (hN : Numbers ρ c x₀ lam B) (l : ℕ) : ∀ k j, j + k = l → 1 ≤ lamAt ρ c x₀ l lam B j := by sorry
