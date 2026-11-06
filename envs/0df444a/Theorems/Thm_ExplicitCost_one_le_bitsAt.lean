-- Prove2me | Theorems.Thm_ExplicitCost_one_le_bitsAt
-- name    : ExplicitCost.one_le_bitsAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:13:15.069196+00:00
-- url     : https://prove2.me/theorems/3e87943f-f3e6-4d93-b6bb-c6697766744f
-- title:
--   Explicit Cost: one le bits At
-- statement:
--   1 ≤ 𝔅_j for every j ≤ ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L112-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L112-L123

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

theorem ExplicitCost.one_le_bitsAt (hN : Numbers ρ c x₀ lam B) (hj : j ≤ l) : 1 ≤ bitsAt ρ c x₀ l lam B j := by sorry
