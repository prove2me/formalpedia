-- Prove2me | Theorems.Thm_ExplicitCost_recursionWithPoly
-- name    : ExplicitCost.recursionWithPoly
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:23:04.990973+00:00
-- url     : https://prove2.me/theorems/dfcdc23c-7844-4c65-993a-6b4bed2c88c7
-- title:
--   Explicit Cost: recursion With Poly
-- statement:
--   **`RecursionWithPoly`**: so has the machine with the algorithm of the pieces built in, and the
--   algorithm of the theorem.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyAll.lean#L35-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PolyAll.lean#L35-L35

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

theorem ExplicitCost.recursionWithPoly : RecursionWithPoly := by sorry
