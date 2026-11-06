-- Prove2me | Theorems.Thm_ExplicitCost_rowWeight_within
-- name    : ExplicitCost.rowWeight_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:08:37.248666+00:00
-- url     : https://prove2.me/theorems/e776e819-983e-4ca5-a045-39f1da2182a9
-- title:
--   Explicit Cost: row Weight within
-- statement:
--   **The procedure for W_a.**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean#L58-L93
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowWeightRun.lean#L58-L93

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_ParentNumbers
import Definitions.Def_CountedRecursion_Within
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowWeightRun
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.rowWeight_within {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hg : 1 ≤ g) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B)
    (a : Fin (nParts g g tr)) {z : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) :
    rowWeight.Within (upOracle D g lam Lam W) (upPrices c tq) (p, (a.val, z)) (g * (tq + 1)) (2 * size (p, (a.val, z)) + 2 * size g + B * g + B + 8) ((patternNet D c g tr lam y W).W a z) := by sorry
