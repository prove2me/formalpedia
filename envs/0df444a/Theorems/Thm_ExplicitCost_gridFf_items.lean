-- Prove2me | Theorems.Thm_ExplicitCost_gridFf_items
-- name    : ExplicitCost.gridFf_items
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:07.569599+00:00
-- url     : https://prove2.me/theorems/e90f2b66-cbc4-4dcb-b65e-0f9401ce452b
-- title:
--   Explicit Cost: grid Ff items
-- statement:
--   `ClauseBound.Alg.gridFf` for the pieces, as the check and the loop of `rowFactor`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean#L84-L108
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean#L84-L108

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowPairRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowFactorRun
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.gridFf_items (hg : 0 < g) {q : FQ} (hb : q.1.2 < nParts g g tr) (hz : q.2.1.length = nMemb g g tr * (g * g) * lam) (hθ : q.2.2.length = capG (piecesOf D c) g g tr 0 lam y q.1.1 q.1.2) :
    gridFf (piecesOf D c) [()] g g tr 0 lam y q = if labelOK g tr lam q = true then ∏ j ∈ range (g * g), factorItem D c g tr lam y q j else 0 := by sorry
