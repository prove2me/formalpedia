-- Prove2me | Theorems.Thm_ExplicitCost_size_units
-- name    : ExplicitCost.size_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:02:02.778709+00:00
-- url     : https://prove2.me/theorems/0cbb71e5-c743-466d-bf82-d573f87f8581
-- title:
--   Explicit Cost: size units
-- statement:
--   The size of a string of units.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverCall.lean#L48-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverCall.lean#L48-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverCall
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l y : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}

theorem ExplicitCost.size_units (u : List Unit) : size u = 2 * u.length + 1 := by sorry
