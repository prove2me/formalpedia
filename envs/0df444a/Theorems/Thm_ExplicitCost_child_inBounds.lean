-- Prove2me | Theorems.Thm_ExplicitCost_child_inBounds
-- name    : ExplicitCost.child_inBounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:10:13.373556+00:00
-- url     : https://prove2.me/theorems/36041fa3-e7fe-4b93-8780-243145463c5b
-- title:
--   Explicit Cost: child in Bounds
-- statement:
--   A callee of an instance within the bounds is within the bounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L81-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/Meets.lean#L81-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_Meets
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l lam B j : ℕ}

theorem ExplicitCost.child_inBounds {a a' : Ctx} (hρ : 1 / 2 ≤ ρ) (hIn : InBounds ρ c x₀ l lam B a) (h1 : 1 ≤ cLam a) (hj : cLev a = j + 1) (hj' : cLev a' = j)
    (hL : (Levels.Gen.K x₀ j : ℝ) ^ 2 * cLam a' ≤ (ρ + 3 * Levels.Gen.zeta j) * ((Levels.Gen.g x₀ j : ℝ) ^ 4 * cLam a) + (c : ℝ) / 4 * (Levels.Gen.g x₀ j : ℝ) ^ 4 * Real.logb 2 (2 * cLam a) + (Levels.Gen.K x₀ j : ℝ) ^ 2)
    (hB : cB a' = bitsOut (Levels.Gen.K x₀ j) (Levels.Gen.g x₀ j) (Levels.Gen.g x₀ j ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ j) (cLam a) (cB a))) : InBounds ρ c x₀ l lam B a' := by sorry
