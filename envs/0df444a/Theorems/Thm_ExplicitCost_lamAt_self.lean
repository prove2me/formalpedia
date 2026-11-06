-- Prove2me | Theorems.Thm_ExplicitCost_lamAt_self
-- name    : ExplicitCost.lamAt_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:09:40.95031+00:00
-- url     : https://prove2.me/theorems/b61b3b36-7a6e-45aa-b0de-fa156a376ae2
-- title:
--   Explicit Cost: lam At self
-- statement:
--   At the depth ℓ the bound for λ is λ itself.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L30-L30
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L30-L30

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

theorem ExplicitCost.lamAt_self (ρ : ℝ) (c x₀ l lam B : ℕ) : lamAt ρ c x₀ l lam B l = lam := by sorry
