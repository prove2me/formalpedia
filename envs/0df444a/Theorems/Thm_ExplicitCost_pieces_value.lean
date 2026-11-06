-- Prove2me | Theorems.Thm_ExplicitCost_pieces_value
-- name    : ExplicitCost.pieces_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:07:49.619917+00:00
-- url     : https://prove2.me/theorems/8fef32d1-55bc-465f-b0a4-bd84401ca1d2
-- title:
--   Explicit Cost: pieces value
-- statement:
--   The pieces answer the question for A_i at four strings of λ bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L36-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/RowPairRun.lean#L36-L41

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

theorem ExplicitCost.pieces_value {i : ℤ} (hi : i ∈ (D.fam lam).I) {s : List Bool × List Bool × List Bool × List Bool} (h1 : s.1.length = lam) (h2 : s.2.1.length = lam) (h3 : s.2.2.1.length = lam) (h4 : s.2.2.2.length = lam)
    (hlam : 1 ≤ lam) (hLam : lam ≤ Lam) {u : List Unit} (hu : u.length = lam) : piecesUpTo D Lam (u, .inr (.inr (.inr (.inl (i, s))))) = some (Sum.inl (pieceValue D lam i s)) := by sorry
