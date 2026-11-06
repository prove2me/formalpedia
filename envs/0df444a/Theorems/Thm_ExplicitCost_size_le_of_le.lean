-- Prove2me | Theorems.Thm_ExplicitCost_size_le_of_le
-- name    : ExplicitCost.size_le_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T08:48:39.730211+00:00
-- url     : https://prove2.me/theorems/2bf4b965-8b01-4abb-b3f1-afd118253e90
-- title:
--   Explicit Cost: size le of le
-- statement:
--   The size of a number grows with the number.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L44-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L44-L44

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

theorem ExplicitCost.size_le_of_le {m n : ℕ} (h : m ≤ n) : size m ≤ size n := by sorry
