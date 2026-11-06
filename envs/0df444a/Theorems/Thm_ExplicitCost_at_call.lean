-- Prove2me | Theorems.Thm_ExplicitCost_at_call
-- name    : ExplicitCost.at_call
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:34:36.342945+00:00
-- url     : https://prove2.me/theorems/75bc845c-3ebc-450e-ad08-5d3825ee33dc
-- title:
--   Explicit Cost: at call
-- statement:
--   **A permitted call**: the callee belongs to a pattern y and to the first grouping x that the
--   test of Lemma 8 accepts on the network with the smaller total, and all of `AtCall` holds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallFacts.lean#L60-L99
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallFacts.lean#L60-L99

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallLemma
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallFacts
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.at_call (hG : GroupingWithCall) (hL : LabelLengthIsL) (hC : CaseTwoApplies) (hBN : BothNetworks) {ρ : ℝ} {c x₀ : ℕ} {D : PiecesCounted.Data} (hS : Setting ρ c x₀ D) {Bound : Ctx → Prop} {a a' : Ctx}
    {f : TableQuery → Option Ans} {l : ℕ} (hF : Fits x₀ a f) (hl : cLev a = l + 1) (hc : (spec D c x₀ Bound).Child a f a') : ∃ y x : ℕ, AtCall D c x₀ l a a' f y x := by sorry
