-- Prove2me | Theorems.Thm_ExplicitCost_mapAsk_poly
-- name    : ExplicitCost.mapAsk_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:15:35.830593+00:00
-- url     : https://prove2.me/theorems/e1dcbdf5-e0e2-4dc1-a73c-016a1c39e5be
-- title:
--   Explicit Cost: map Ask poly
-- statement:
--   Queries rewritten by a polynomial-time function.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L40-L42
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyRules.lean#L40-L42

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

theorem ExplicitCost.mapAsk_poly {h : Q → Q'} (hh : PolyT h) {M : QueryMachine Q A α β} (hM : M.PolyTimeSteps) : (QueryMachine.mapAsk h M).PolyTimeSteps := by sorry
