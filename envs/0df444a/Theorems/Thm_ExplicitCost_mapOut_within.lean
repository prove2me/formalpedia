-- Prove2me | Theorems.Thm_ExplicitCost_mapOut_within
-- name    : ExplicitCost.mapOut_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:41:47.990964+00:00
-- url     : https://prove2.me/theorems/a03a49ef-7ccb-427b-94bd-d47376ce0e9d
-- title:
--   Explicit Cost: map Out within
-- statement:
--   A function applied to the result.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L46-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L46-L48

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Definitions.Def_QueryMachines_CombRuns
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Within
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Finset
variable {Q Q' A A' α α₁ α₂ β γ : Type}

theorem ExplicitCost.mapOut_within {M : QueryMachine Q A α β} {g : β → γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {b : β} (h : M.Within O w a T S b) : (QueryMachine.mapOut M g).Within O w a T S (g b) := by sorry
