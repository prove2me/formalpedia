-- Prove2me | Theorems.Thm_ExplicitCost_pair_row
-- name    : ExplicitCost.pair_row
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:17:57.129716+00:00
-- url     : https://prove2.me/theorems/5ac4c616-606d-4b19-a589-16a6fe901031
-- title:
--   Explicit Cost: pair row
-- statement:
--   Ψ_{a,a'} of the row network, for a < a'.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternPsi.lean#L85-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternPsi.lean#L85-L101

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_GridLemmas
import Definitions.Def_ClauseBound_Alg_GridPresents
import Definitions.Def_StepMachines_Prog_SidePresents
import Definitions.Def_Groundwork_Grid_RowNet
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternPsi
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.pair_row {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {g lam : ℕ} (hlam : 1 ≤ lam) (y : ℕ) (Rm : Inst (Fin (g * g)) (List Bool)) {a b : Fin g} (hab : a < b) {z z' : List Bool}
    (hz : z.length = g * (g * g) * lam) (hz' : z'.length = g * (g * g) * lam) :
    (gridN (piecesOf D c) [()] g g false 0 lam y Rm).Ψ a b z z' =
      (∏ i : Fin g, if heG g g lam z i (nodeG g false b i) = heG g g lam z' i (nodeG g false a i) then 1 else 0) *
        ∏ k : Fin g × Fin g with k.1 < k.2, pieceValue D lam (indexAt D lam (digG (piecesOf D c) g false 0 lam y (tri a.val b.val) (tri k.1 k.2))) (rectStrings g false lam ((a.val, b.val), (z, z')) k.1 k.2) := by sorry
