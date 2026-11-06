-- Prove2me | Theorems.Thm_ExplicitCost_solver_room
-- name    : ExplicitCost.solver_room
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T09:14:51.773924+00:00
-- url     : https://prove2.me/theorems/427d4a31-5461-47cb-a383-c2d67e061873
-- title:
--   Explicit Cost: solver room
-- statement:
--   **The room of the solver**, and the two small counts: one exponent for all, which depends on c,
--   Cn, Cg only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L116-L190
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/SolverRoom.lean#L116-L190

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_SolverCall
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_SolverRoom
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.solver_room (hFew : PatternsFew) (hCr : CrudeBounds) (c Cn Cg : ℕ) : ∃ C : ℕ, ∀ (ρ : ℝ) (x₀ : ℕ) (D : PiecesCounted.Data), Setting ρ c x₀ D → ∀ (a : Ctx) (l : ℕ), 1 ≤ cLam a → 1 ≤ cB a → cLev a = l + 1 →
    20 * (Cn * Levels.Gen.g x₀ l + size (readyOf D x₀ a.1) + size (nPatterns (readyOf D x₀ a.1)) + size (nPatterns (readyOf D x₀ a.1) * 2 ^ (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)))) + (Levels.Gen.g x₀ l * ((Levels.Gen.g x₀ l ^ 3 * cLam a) + (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size ((1 : ℕ), 2 ^ (l + 5))) ^ Cg + (Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + Levels.Gen.g x₀ l * Levels.Gen.g x₀ l * (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a))) + size (Levels.Gen.K x₀ l ^ Levels.Gen.g x₀ l) + Levels.Gen.g x₀ l + Levels.Gen.g x₀ l * (Levels.Gen.g x₀ l ^ 3 * cLam a) + bitsOut (Levels.Gen.K x₀ l) (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l ^ 3 * cLam a) (bitsOne c (Levels.Gen.g x₀ l) (cLam a) (cB a)) + 4) ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C ∧
    Cg + 3 ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C ∧ 2 * l + 7 + 2 * #(D.fam (cLam a)).I ≤ Xi (Levels.Gen.g x₀ l) (cLam a) (cB a) ^ C := by sorry
