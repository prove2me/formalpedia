-- Prove2me | Theorems.Thm_ExplicitCost_recursionWithPoly_of
-- name    : ExplicitCost.recursionWithPoly_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:22:36.50122+00:00
-- url     : https://prove2.me/theorems/33e462ba-f0b6-41a5-9875-ae3decfdd204
-- title:
--   Explicit Cost: recursion With Poly of
-- statement:
--   `RecursionWithPoly`, given that the recursion has polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyEnd.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyEnd.lean#L38-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RecursionDefs
import Definitions.Def_CountedRecursion_PolyProcedure
import Definitions.Def_CountedRecursion_PolySolver
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyEnd
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed

theorem ExplicitCost.recursionWithPoly_of (h : ∀ c x₀ : ℕ, (recursion c x₀).PolyTimeSteps) : RecursionWithPoly := by sorry
