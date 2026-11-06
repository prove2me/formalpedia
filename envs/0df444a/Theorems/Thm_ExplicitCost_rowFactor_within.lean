-- Prove2me | Theorems.Thm_ExplicitCost_rowFactor_within
-- name    : ExplicitCost.rowFactor_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:21.221792+00:00
-- url     : https://prove2.me/theorems/dea01da8-2254-45b8-8e31-40f32b15b110
-- title:
--   Explicit Cost: row Factor within
-- statement:
--   **The procedure for f_{a,a'}.**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean#L111-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowFactorRun.lean#L111-L173

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

theorem ExplicitCost.rowFactor_within (hLA : ListsAgree) {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hY : pY p = y) (hLs : pLists p = listsOf D lam) (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hLam : lam ≤ Lam)
    {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool} (hz : z.length = nMemb g g tr * (g * g) * lam) (hθ : θ.length = capG (piecesOf D c) g g tr 0 lam y a b) :
    rowFactor.Within (upOracle D g lam Lam W) (upPrices c tq) (p, ((a.val, b.val), (z, θ))) (g * g * (askCost c lam + 1))
      (2 * size (p, ((a.val, b.val), (z, θ))) + 2 * size (g * g) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + 9) ((patternNet D c g tr lam y W).f a b z θ) := by sorry
