-- Prove2me | Theorems.Thm_ExplicitCost_foldl_append_toNat
-- name    : ExplicitCost.foldl_append_toNat
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:16.815594+00:00
-- url     : https://prove2.me/theorems/6f882073-17db-4e46-979b-2feac86d2697
-- title:
--   Explicit Cost: foldl append to Nat
-- statement:
--   The loop that appends one number in each round makes the list of the numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L85-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStages.lean#L85-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverDefs
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStages
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork QueryMachines Printed
variable {Q α : Type}

theorem ExplicitCost.foldl_append_toNat (v : ℕ → ℤ) (k : ℕ) : (List.range k).foldl (fun (acc : List ℕ) y => acc ++ [(v y).toNat]) [] = (List.range k).map fun y => (v y).toNat := by sorry
