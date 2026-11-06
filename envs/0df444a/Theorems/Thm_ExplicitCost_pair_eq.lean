-- Prove2me | Theorems.Thm_ExplicitCost_pair_eq
-- name    : ExplicitCost.pair_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:25:57.363992+00:00
-- url     : https://prove2.me/theorems/b483a244-2710-4dea-b2ba-7f2b7520a341
-- title:
--   Explicit Cost: pair eq
-- statement:
--   **Ψ_{a,a'}(z, z')** for a ≠ a', as `rowPair` computes it: the query is put in order, then the
--   check and the product.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L89-L103
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternValues.lean#L89-L103

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternPsi
import Definitions.Def_Printed_Coding
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternValues
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {D : PiecesCounted.Data} {c g lam y : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.pair_eq (hPP : PairIsProduct) {ρ : ℝ} {x₀ : ℕ} (hS : Setting ρ c x₀ D) (hg : 2 ≤ g) (hlam : 1 ≤ lam) (hy : y < #(D.fam lam).I ^ nRectG g g) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z z' : List Bool}
    (hz : z ∈ (patternNet D c g tr lam y W).S a) (hz' : z' ∈ (patternNet D c g tr lam y W).S b) :
    (patternNet D c g tr lam y W).Ψ a b z z' = if straightOK g tr lam (ordered ((a.val, b.val), (z, z'))) = true then
      ∏ j ∈ range (g * g), (if j / g < j % g then
        pieceValue D lam (indexAt D lam (digG (piecesOf D c) g tr 0 lam y (tri (ordered ((a.val, b.val), (z, z'))).1.1 (ordered ((a.val, b.val), (z, z'))).1.2) (tri (j / g) (j % g))))
          (rectStrings g tr lam (ordered ((a.val, b.val), (z, z'))) (j / g) (j % g)) else 1)
    else 0 := by sorry
