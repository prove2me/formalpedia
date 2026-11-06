-- Prove2me | Theorems.Thm_ExplicitCost_pointQuery_ok
-- name    : ExplicitCost.pointQuery_ok
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:25:38.934389+00:00
-- url     : https://prove2.me/theorems/eb6e1b54-347c-4be5-9861-8e7d711e3164
-- title:
--   Explicit Cost: point Query ok
-- statement:
--   The query to the tables at the grid point number i of the row a is a legitimate one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L42-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L42-L50

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternValues
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.pointQuery_ok (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) {i : ℕ} (hi : i < nMemb g g tr) :
    (toTable (pointQuery g tr lam (a.val, z) i)).1 < g * g ∧ (toTable (pointQuery g tr lam (a.val, z) i)).2.length = (g * g - 1) * lam := by sorry
