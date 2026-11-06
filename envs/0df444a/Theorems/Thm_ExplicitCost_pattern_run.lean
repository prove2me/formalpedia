-- Prove2me | Theorems.Thm_ExplicitCost_pattern_run
-- name    : ExplicitCost.pattern_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:09:32.652397+00:00
-- url     : https://prove2.me/theorems/af615a79-2f1e-4f22-b1fb-283b4aa420f5
-- title:
--   Explicit Cost: pattern run
-- statement:
--   **The run for one pattern.**
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverCall.lean#L80-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverCall.lean#L80-L137

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverPattern
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverCall
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l y : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}

theorem ExplicitCost.pattern_run (hGW : GroupingWithCall) (hLL : LabelLengthIsL) (hV : ValueIsKept) (hBN : BothNetworks) (hC2 : CaseTwoApplies) (hSub : QueryMachines.StSubstWithin) (c : ℕ) :
    ∃ Cg : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (Bound : Ctx → Prop) (a : Ctx) (f : TableQuery → Option Ans) (l : ℕ), Fits x₀ a f → cLev a = l + 1 → ∀ y < nPatterns (readyOf D x₀ a.1),
      (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value.natAbs ≤ 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) ∧
      ∀ tc tq Lam : ℕ, (patternValue c).Within ((spec D c x₀ Bound).oracle (piecesUpTo D Lam) a f) (solPrices c tc tq) (readyOf D x₀ a.1, y) (Cg * Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l + (tc + 2))
        ((Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg + (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + 2 * (2 * size (readyOf D x₀ a.1) + 2 * size (nPatterns (readyOf D x₀ a.1)) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + 2 * Levels.Gen.g x₀ l + 6 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) + 2 * bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 12)) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).value := by sorry
