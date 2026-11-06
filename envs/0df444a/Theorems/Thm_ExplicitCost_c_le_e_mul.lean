-- Prove2me | Theorems.Thm_ExplicitCost_c_le_e_mul
-- name    : ExplicitCost.c_le_e_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:28:55.081314+00:00
-- url     : https://prove2.me/theorems/b91304c7-cd81-4601-805a-012fded006e7
-- title:
--   Explicit Cost: c le e mul
-- statement:
--   c ≤ e_jK_j².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RoomWithin.lean#L44-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RoomWithin.lean#L44-L65

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_LevelBound
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RoomWithin
set_option autoImplicit false
section
section
open ExplicitCost
open Levels.Gen Printed Finset

theorem ExplicitCost.c_le_e_mul (hLv : ChainLevels) (hA : Levels.Gen.PartA) {ρ : ℝ} {c x₀ lam B : ℕ} (hN : Numbers ρ c x₀ lam B) (j : ℕ) : (c : ℝ) ≤ e ρ x₀ j * (K x₀ j : ℝ) ^ 2 := by sorry
