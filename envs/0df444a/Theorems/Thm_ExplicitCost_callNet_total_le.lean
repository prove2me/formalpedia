-- Prove2me | Theorems.Thm_ExplicitCost_callNet_total_le
-- name    : ExplicitCost.callNet_total_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:41:15.826217+00:00
-- url     : https://prove2.me/theorems/cd9f384c-7e4e-4a3b-93d4-b82ce155ea67
-- title:
--   Explicit Cost: call Net total le
-- statement:
--   U = min(U^row, U^col) ≤ … ≤ N(ρ + 1/g) + (c/4)g⁴log(2λ), for the network that the solver takes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChildIsGood.lean#L33-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/ChildIsGood.lean#L33-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallFacts
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_ChildIsGood
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.callNet_total_le (hT : TotalsAre) (hSm : SmallerTotal) {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {a : Ctx} (f : TableQuery → Option Ans) {l y : ℕ} (hl : cLev a = l + 1) (hlam : 1 ≤ cLam a)
    (hy : y < #(D.fam (cLam a)).I ^ nRectG (Levels.Gen.g x₀ l) (Levels.Gen.g x₀ l)) :
    ((callNet D c x₀ l a f y).U : ℝ) ≤ (Levels.Gen.g x₀ l : ℝ) ^ 4 * cLam a * (ρ + 1 / Levels.Gen.g x₀ l) + (c : ℝ) / 4 * (Levels.Gen.g x₀ l : ℝ) ^ 4 * Real.logb 2 (2 * cLam a) := by sorry
