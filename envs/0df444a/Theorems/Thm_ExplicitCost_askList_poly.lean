-- Prove2me | Theorems.Thm_ExplicitCost_askList_poly
-- name    : ExplicitCost.askList_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:19:20.798197+00:00
-- url     : https://prove2.me/theorems/2bedf97f-3f76-4e46-9bf2-0d6f6f6b5aae
-- title:
--   Explicit Cost: ask List poly
-- statement:
--   One query, its answer read as a list of integers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L113-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L113-L113

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

theorem ExplicitCost.askList_poly [HasSize α] [Carried α] {h : α → Q} (hh : PolyT h) : (askList h).PolyTimeSteps := by sorry
