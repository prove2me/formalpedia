-- Prove2me | Theorems.Thm_ExplicitCost_division_exact
-- name    : ExplicitCost.division_exact
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:12:26.420033+00:00
-- url     : https://prove2.me/theorems/f24b95ce-a465-4ef3-a1a8-f21eef2c9ed6
-- title:
--   Explicit Cost: division exact
-- statement:
--   «Thus d^{|ℛ|}Z = Σ_ι Z_ι»: the sum of the Z_ι, divided by d^{|ℛ|}, is the value of the instance.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStep.lean#L45-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverStep.lean#L45-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverRoom
import Definitions.Def_CountedRecursion_GridLemmas
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverStep
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}

theorem ExplicitCost.division_exact (hExp : Expansion) (hS : Setting ρ c x₀ D) (Bound : Ctx → Prop) (hF : Fits x₀ a f) (hl : cLev a = l + 1) :
    (spec D c x₀ Bound).val a f = Sum.inl ((∑ y ∈ range (nPatterns (readyOf D x₀ a.1)), (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value) / (((rD (readyOf D x₀ a.1)).toNat ^ rRect (readyOf D x₀ a.1) : ℕ) : ℤ)) := by sorry
