-- Prove2me | Theorems.Thm_ExplicitCost_query_poly
-- name    : ExplicitCost.query_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:42:09.45711+00:00
-- url     : https://prove2.me/theorems/43991ebd-b56f-42f0-8806-aa241a415adf
-- title:
--   Explicit Cost: query poly
-- statement:
--   A single query, computed in polynomial time from the input.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L37-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L37-L37

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_Answers
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyRules
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines QueryMachines.QueryMachine Printed
variable {Q Q' A A' C α α₁ α₂ β γ : Type} [Enc Q] [Enc Q'] [Enc A] [Enc A'] [Enc α] [Enc α₁] [Enc α₂] [Enc β] [Enc γ]

theorem ExplicitCost.query_poly [HasSize α] [HasSize A] [Carried α] [Carried A] {h : α → Q} (hh : PolyT h) : (QueryMachine.query h : QueryMachine Q A α A).PolyTimeSteps := by sorry
