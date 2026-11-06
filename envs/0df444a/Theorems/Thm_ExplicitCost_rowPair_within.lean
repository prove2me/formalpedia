-- Prove2me | Theorems.Thm_ExplicitCost_rowPair_within
-- name    : ExplicitCost.rowPair_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:08:29.586364+00:00
-- url     : https://prove2.me/theorems/48cdccfa-a75f-4e3f-b0a7-b9ed249f3236
-- title:
--   Explicit Cost: row Pair within
-- statement:
--   **The procedure for Ψ_{a,a'}.**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L126-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L126-L139

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowPairRun
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.rowPair_within (hPP : PairIsProduct) (hLA : ListsAgree) {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hY : pY p = y) (hLs : pLists p = listsOf D lam) (hS : Setting ρ c x₀ D) (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hLam : lam ≤ Lam)
    (hy : y < #(D.fam lam).I ^ nRectG g g) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool} (hz : z ∈ (patternNet D c g tr lam y W).S a) (hz' : z' ∈ (patternNet D c g tr lam y W).S b) :
    rowPair.Within (upOracle D g lam Lam W) (upPrices c tq) (p, ((a.val, b.val), (z, z'))) (g * g * (askCost c lam + 1))
      (2 * size (p, ((a.val, b.val), (z, z'))) + 2 * size (g * g) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + 9) ((patternNet D c g tr lam y W).Ψ a b z z') := by sorry
