-- Prove2me | Theorems.Thm_ExplicitCost_sized_zero
-- name    : ExplicitCost.sized_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:28:26.736806+00:00
-- url     : https://prove2.me/theorems/41aba2af-ecdd-4f06-8eb3-b70f5b91aa07
-- title:
--   Explicit Cost: sized zero
-- statement:
--   The network for tables that are 0: its sizes, from `gridN_sized`.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L38-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L38-L40

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternValues
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternIs
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.sized_zero (hS : Setting ρ c x₀ D) (hlam : 1 ≤ lam) :
    (gridN (piecesOf D c) [()] g g tr 0 lam y fun _ _ => 0).Sized (1 * (nParts g g tr * nMemb g g tr ^ 2 * lam)) (nMemb g g tr * 0 + nMemb g g tr ^ 2 * (2 * lam) ^ c) := by sorry
