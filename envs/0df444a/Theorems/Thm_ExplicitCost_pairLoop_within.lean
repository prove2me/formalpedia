-- Prove2me | Theorems.Thm_ExplicitCost_pairLoop_within
-- name    : ExplicitCost.pairLoop_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:03.261334+00:00
-- url     : https://prove2.me/theorems/ce1af3d2-d4bb-4e61-a86a-ad804025897e
-- title:
--   Explicit Cost: pair Loop within
-- statement:
--   The check and the loop, run.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L74-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L74-L123

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_RowWeightRun
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_RowPairRun
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B tq Lam : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.pairLoop_within (hLA : ListsAgree) {p : Parent} (hG : pG p = g) (hL : pLam p = lam) (hT : pTr p = tr) (hY : pY p = y) (hLs : pLists p = listsOf D lam) (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hLam : lam ≤ Lam)
    {q : PsiQ} (ha : q.1.1 < nParts g g tr) (hb : q.1.2 < nParts g g tr) (hz : q.2.1.length = nMemb g g tr * (g * g) * lam) (hz' : q.2.2.length = nMemb g g tr * (g * g) * lam) :
    pairLoop.Within (upOracle D g lam Lam W) (upPrices c tq) (p, q) (g * g * (askCost c lam + 1)) (2 * size (p, q) + 2 * size (g * g) + (2 * lam) ^ c * (g * g) + (2 * lam) ^ c + 9)
      (if straightOK g tr lam q = true then ∏ j ∈ range (g * g), pairItem D c g tr lam y q j else 0) := by sorry
