-- Prove2me | Theorems.Thm_ExplicitCost_mapIn_within
-- name    : ExplicitCost.mapIn_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:42:13.392159+00:00
-- url     : https://prove2.me/theorems/022837ae-9444-4bc4-a065-418d10a779c6
-- title:
--   Explicit Cost: map In within
-- statement:
--   A function applied to the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L41-L43
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L41-L43

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

theorem ExplicitCost.mapIn_within {g : α → β} {M : QueryMachine Q A β γ} {O : Q → Option A} {w : Q → ℕ} {a : α} {T S : ℕ} {c : γ} (h : M.Within O w (g a) T S c) : (QueryMachine.mapIn g M).Within O w a T S c := by sorry
