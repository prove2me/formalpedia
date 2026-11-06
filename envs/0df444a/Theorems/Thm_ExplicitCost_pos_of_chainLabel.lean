-- Prove2me | Theorems.Thm_ExplicitCost_pos_of_chainLabel
-- name    : ExplicitCost.pos_of_chainLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:18:52.988318+00:00
-- url     : https://prove2.me/theorems/f4d97e19-9080-45d9-9745-72f45a5991d4
-- title:
--   Explicit Cost: pos of chain Label
-- statement:
--   1 ≤ Λ_j, 𝔅_j for j ≤ ℓ, from `ChainLabel` (for j < ℓ) and the hypotheses on λ and B (for j = ℓ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L29-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/LevelBound.lean#L29-L34

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Chain
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_LevelBound
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}

theorem ExplicitCost.pos_of_chainLabel (hL : ChainLabel) (hN : Numbers ρ c x₀ lam B) (hj : j ≤ l) : 1 ≤ lamAt ρ c x₀ l lam B j ∧ 1 ≤ bitsAt ρ c x₀ l lam B j := by sorry
