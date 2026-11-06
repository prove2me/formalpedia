-- Prove2me | Theorems.Thm_ExplicitCost_recursion_poly
-- name    : ExplicitCost.recursion_poly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:23:00.201024+00:00
-- url     : https://prove2.me/theorems/d703ba9e-d101-40f4-a9fb-69ad686b8080
-- title:
--   Explicit Cost: recursion poly
-- statement:
--   The one machine for all levels has polynomial-time steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyAll.lean#L31-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyAll.lean#L31-L31

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PolyEnd
import Definitions.Def_ExplicitCost_GroupingPoly
import Definitions.Def_Tower_PolyTower
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PolyAll
set_option autoImplicit false
section
section
open ExplicitCost
open Groundwork QueryMachines Printed

theorem ExplicitCost.recursion_poly (c x₀ : ℕ) : (recursion c x₀).PolyTimeSteps := by sorry
