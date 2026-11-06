-- Prove2me | Theorems.Thm_ExplicitCost_abs_factor_lt
-- name    : ExplicitCost.abs_factor_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:31:40.71419+00:00
-- url     : https://prove2.me/theorems/8e7eb361-30c5-42b6-86c7-b3aaa5a51fcb
-- title:
--   Explicit Cost: abs factor lt
-- statement:
--   |f_{a,a'}| < 2^{B₁}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L51-L56
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L51-L56

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_PatternValues
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_PatternIs
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet ClauseBound.Alg.GridPresents Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {D : PiecesCounted.Data} {c x₀ g lam y B : ℕ} {tr : Bool} {W : ℕ → List Bool → ℤ}

theorem ExplicitCost.abs_factor_lt (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) {a b : Fin (nParts g g tr)} (hab : a ≠ b) {z θ : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) (hθ : θ.length = capG (piecesOf D c) g g tr 0 lam y a b) : |(patternNet D c g tr lam y W).f a b z θ| < 2 ^ bitsOne c g lam B := by sorry
