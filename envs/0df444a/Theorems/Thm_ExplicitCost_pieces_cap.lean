-- Prove2me | Theorems.Thm_ExplicitCost_pieces_cap
-- name    : ExplicitCost.pieces_cap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:15:40.314106+00:00
-- url     : https://prove2.me/theorems/cee7c256-d07e-41c8-a6e5-e228a85dc284
-- title:
--   Explicit Cost: pieces cap
-- statement:
--   The question for c^row_i or c^col_i, i the element number j of 𝓘.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStep.lean#L36-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStep.lean#L36-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverRoom
import Definitions.Def_CountedRecursion_GridLemmas
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStep
import Theorems.Thm_Groundwork_PolyT_length
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.length
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.pieces_cap (D : PiecesCounted.Data) (lam : ℕ) (tr : Bool) {j : ℕ} (hj : j < ((D.fam lam).I.sort).length) :
    D.answer lam (.inr (.inr (.inl (tr, ((D.fam lam).I.sort).getD j 0)))) = some (.inl (((((D.fam lam).I.sort).map fun i => D.cap lam tr i).getD j 0 : ℕ) : ℤ)) := by sorry
