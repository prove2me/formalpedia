-- Prove2me | Theorems.Thm_ExplicitCost_pattern_is
-- name    : ExplicitCost.pattern_is
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:29:30.873994+00:00
-- url     : https://prove2.me/theorems/8683a35e-5da6-4a66-ac5a-34573657a9ab
-- title:
--   Explicit Cost: pattern is
-- statement:
--   **The network is a network with the parameters P = g³λ and B₁ = gB + g²(2λ)^c.**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L103-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L103-L124

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

theorem ExplicitCost.pattern_is (hS : Setting ρ c x₀ D) (hg : 1 ≤ g) (hlam : 1 ≤ lam) (hB : 1 ≤ B) (hW : ∀ w < g * g, ∀ z ∈ words ((g * g - 1) * lam), |W w z| < 2 ^ B) :
    (patternNet D c g tr lam y W).Is (g ^ 3 * lam) (bitsOne c g lam B) := by sorry
