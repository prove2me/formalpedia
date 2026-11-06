-- Prove2me | Theorems.Thm_ExplicitCost_query_within
-- name    : ExplicitCost.query_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:42:01.016202+00:00
-- url     : https://prove2.me/theorems/1a7fdc26-8cb6-43d0-b148-74382d2bf937
-- title:
--   Explicit Cost: query within
-- statement:
--   One query: its price.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L36-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Within.lean#L36-L38

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

theorem ExplicitCost.query_within [HasSize α] [HasSize A] {h : α → Q} {O : Q → Option A} {w : Q → ℕ} {a : α} {v : A} (hv : O (h a) = some v) :
    (QueryMachine.query h : QueryMachine Q A α A).Within O w a (w (h a)) (max (size a) (size v) + 1) v := by sorry
