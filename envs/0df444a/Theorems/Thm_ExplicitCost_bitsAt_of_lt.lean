-- Prove2me | Theorems.Thm_ExplicitCost_bitsAt_of_lt
-- name    : ExplicitCost.bitsAt_of_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:13:58.77833+00:00
-- url     : https://prove2.me/theorems/6addb942-88dc-4f67-bdb6-d0a6e267feae
-- title:
--   Explicit Cost: bits At of lt
-- statement:
--   𝔅_j from Λ_{j+1} and 𝔅_{j+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L46-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L46-L53

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

theorem ExplicitCost.bitsAt_of_lt (ρ : ℝ) (c x₀ lam B : ℕ) (h : j < l) : bitsAt ρ c x₀ l lam B j =
    bitsOut (K x₀ j) (g x₀ j) (g x₀ j ^ 3 * lamAt ρ c x₀ l lam B (j + 1)) (bitsOne c (g x₀ j) (lamAt ρ c x₀ l lam B (j + 1)) (bitsAt ρ c x₀ l lam B (j + 1))) := by sorry
