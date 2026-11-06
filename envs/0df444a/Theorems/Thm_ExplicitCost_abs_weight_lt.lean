-- Prove2me | Theorems.Thm_ExplicitCost_abs_weight_lt
-- name    : ExplicitCost.abs_weight_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:28:55.304199+00:00
-- url     : https://prove2.me/theorems/dd8c6dcc-af11-4bb1-8eb8-b0960c17ffaf
-- title:
--   Explicit Cost: abs weight lt
-- statement:
--   |W_a| < 2^{B₁}: a product of g entries below 2^B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L82-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L82-L100

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

theorem ExplicitCost.abs_weight_lt (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) (a : Fin (nParts g g tr)) {z : List Bool}
    (hz : z.length = nMemb g g tr * (g * g) * lam) : |(patternNet D c g tr lam y W).W a z| < 2 ^ bitsOne c g lam B := by sorry
