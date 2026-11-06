-- Prove2me | Theorems.Thm_ExplicitCost_pattern_input
-- name    : ExplicitCost.pattern_input
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:00:51.884104+00:00
-- url     : https://prove2.me/theorems/e26e739c-4440-45fe-83ce-c0f03975b948
-- title:
--   Explicit Cost: pattern input
-- statement:
--   The network of the pattern y is a network with P = g³λ and B₁; the solver hands over the input
--   that belongs to it, with ζ = 1/2^{ℓ+5} and K_ℓ; the label length computed from it is the L of the
--   lemma; and L ≤ 3gP.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L117-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverPattern.lean#L117-L139

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CliqueReads
import Definitions.Def_CountedRecursion_SolverStages
import Definitions.Def_CountedRecursion_LevelNumbers
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverPattern
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed
variable {ρ : ℝ} {c x₀ l y : ℕ} {D : PiecesCounted.Data} {a : Ctx} {f : TableQuery → Option Ans}

theorem ExplicitCost.pattern_input (hLL : LabelLengthIsL) (hBN : BothNetworks) (hS : Setting ρ c x₀ D) (hF : Fits x₀ a f) (hl : cLev a = l + 1) (hy : y < nPatterns (readyOf D x₀ a.1)) :
    (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).Is (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) ∧
    searchInput c (readyOf D x₀ a.1, y) = groupingInput 1 (2 ^ (l + 5)) (Levels.Gen.K x₀ l) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) ∧
    labelLength (searchInput c (readyOf D x₀ a.1, y)) = AppRunningTime.Lof (Levels.Gen.K x₀ l) (nParts (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y))) (((1 : ℕ) : ℝ) / ((2 ^ (l + 5) : ℕ) : ℝ)) (Levels.Gen.g x₀ l ^ 3 * cLam a) (patternNet D c (Levels.Gen.g x₀ l) (direction (readyOf D x₀ a.1, y)) (cLam a) y (readTables f)).U ∧
    labelLength (searchInput c (readyOf D x₀ a.1, y)) ≤ 3 * (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a)) := by sorry
