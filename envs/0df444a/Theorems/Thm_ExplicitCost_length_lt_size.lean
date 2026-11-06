-- Prove2me | Theorems.Thm_ExplicitCost_length_lt_size
-- name    : ExplicitCost.length_lt_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:06:26.441196+00:00
-- url     : https://prove2.me/theorems/a4ab0964-2be0-47c8-b135-aa401172f74d
-- title:
--   Explicit Cost: length lt size
-- statement:
--   A list has at most as many elements as its size.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L61-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L61-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_Prog_length_lt_size
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}

theorem ExplicitCost.length_lt_size [HasSize α] (l : List α) : l.length < size l := by sorry
