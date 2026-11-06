-- Prove2me | Theorems.Thm_ExplicitCost_map_range_getD
-- name    : ExplicitCost.map_range_getD
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:06:46.622048+00:00
-- url     : https://prove2.me/theorems/4f12f5e9-cd24-4f42-ad26-f6b5447c3319
-- title:
--   Explicit Cost: map range get D
-- statement:
--   The first k elements, read off by their places.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L75-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L75-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}

theorem ExplicitCost.map_range_getD (l : List α) (d : α) {k : ℕ} (hk : k ≤ l.length) : (List.range k).map (fun j => l.getD j d) = l.take k := by sorry
