-- Prove2me | Theorems.Thm_ExplicitCost_pair_fact
-- name    : ExplicitCost.pair_fact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:31:08.376291+00:00
-- url     : https://prove2.me/theorems/5e090cec-e95e-41a0-a3ea-e988ef6c6b9f
-- title:
--   Explicit Cost: pair fact
-- statement:
--   Ψ is the sum over θ ∈ {0,1}^{c_{a,a'}} of the products of the two functions of the
--   factorization.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L60-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/PatternIs.lean#L60-L65

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

theorem ExplicitCost.pair_fact {a b : Fin (nParts g g tr)} (hab : a ≠ b) (z z' : List Bool) :
    (patternNet D c g tr lam y W).Ψ a b z z' = ∑ θ ∈ words ((patternNet D c g tr lam y W).c a b), (patternNet D c g tr lam y W).f a b z θ * (patternNet D c g tr lam y W).f b a z' θ := by sorry
