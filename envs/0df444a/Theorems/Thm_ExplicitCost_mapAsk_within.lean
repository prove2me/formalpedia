-- Prove2me | Theorems.Thm_ExplicitCost_mapAsk_within
-- name    : ExplicitCost.mapAsk_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:58:56.059525+00:00
-- url     : https://prove2.me/theorems/1236169e-6cfa-409a-87bc-6f34651c1fa2
-- title:
--   Explicit Cost: map Ask within
-- statement:
--   Queries rewritten by h: oracle and prices are read through h.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L51-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L51-L54

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

theorem ExplicitCost.mapAsk_within {h : Q → Q'} {M : QueryMachine Q A α β} {O : Q' → Option A} {w : Q' → ℕ} {a : α} {T S : ℕ} {b : β} (hr : M.Within (fun x => O (h x)) (fun x => w (h x)) a T S b) :
    (QueryMachine.mapAsk h M).Within O w a T S b := by sorry
