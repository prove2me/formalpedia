-- Prove2me | Theorems.Thm_ExplicitCost_bitsAt_self
-- name    : ExplicitCost.bitsAt_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:12:57.541239+00:00
-- url     : https://prove2.me/theorems/0ce470a4-faed-4fda-b852-c5f41a385ccf
-- title:
--   Explicit Cost: bits At self
-- statement:
--   At the depth ℓ the bound for B is B itself.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L33-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChainLabel.lean#L33-L33

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

theorem ExplicitCost.bitsAt_self (ρ : ℝ) (c x₀ l lam B : ℕ) : bitsAt ρ c x₀ l lam B l = B := by sorry
