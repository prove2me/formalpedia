-- Prove2me | Theorems.Thm_ExplicitCost_size_mem_le
-- name    : ExplicitCost.size_mem_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:06:26.044257+00:00
-- url     : https://prove2.me/theorems/03c97482-4a83-405e-b4d9-a9ba570db77a
-- title:
--   Explicit Cost: size mem le
-- statement:
--   An element is not larger than the list.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L50-L58
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L50-L58

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

theorem ExplicitCost.size_mem_le [HasSize α] {l : List α} {x : α} (h : x ∈ l) : size x ≤ size l := by sorry
