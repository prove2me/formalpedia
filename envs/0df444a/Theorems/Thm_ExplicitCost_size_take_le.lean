-- Prove2me | Theorems.Thm_ExplicitCost_size_take_le
-- name    : ExplicitCost.size_take_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:13.429123+00:00
-- url     : https://prove2.me/theorems/cc5ddcb8-f2d5-46b6-b4a0-63b779df268c
-- title:
--   Explicit Cost: size take le
-- statement:
--   The first k elements are not larger than the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L69-L72
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L69-L72

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}

theorem ExplicitCost.size_take_le [HasSize α] (l : List α) (k : ℕ) : size (l.take k) ≤ size l := by sorry
