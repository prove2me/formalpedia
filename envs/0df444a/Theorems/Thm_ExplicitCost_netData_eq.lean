-- Prove2me | Theorems.Thm_ExplicitCost_netData_eq
-- name    : ExplicitCost.netData_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:39:38.693195+00:00
-- url     : https://prove2.me/theorems/52962591-985e-42fc-8093-47219f1d1fd4
-- title:
--   Explicit Cost: net Data eq
-- statement:
--   **The input that the procedure writes is the input that belongs to the network.**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentNumbers.lean#L71-L82
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ParentNumbers.lean#L71-L82

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternIs
import Definitions.Def_Printed_GroupingProcs
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ParentNumbers
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ K g lam B y x : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.netData_eq (hLA : ListsAgree) (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) :
    netData c (mkParent D K g lam B tr y x) = ((unary K, unary g), netInput (patternNet D c g tr lam y W) (g ^ 3 * lam) (bitsOne c g lam B)) := by sorry
