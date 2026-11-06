-- Prove2me | Theorems.Thm_ExplicitCost_answerCall_within
-- name    : ExplicitCost.answerCall_within
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:41:32.255839+00:00
-- url     : https://prove2.me/theorems/654ea9bb-93d6-4436-ad67-f90267f407d5
-- title:
--   Explicit Cost: answer Call within
-- statement:
--   **«run the given algorithm on it, and answer each query by computing the entry»**: for a
--   grouping number x with the two properties, the call of x, carried out by E with its queries answered
--   by `entryData`, returns the value of the clique of the groups within 𝒯·(t + 2) operations, t the
--   cost of an entry.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingLemma.lean#L112-L150
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/GroupingLemma.lean#L112-L150

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_GroupingDefs
import Definitions.Def_ExplicitCost_GroupingNumbers
import Definitions.Def_ExplicitCost_GroupingSearch
import Definitions.Def_ExplicitCost_GroupingCall
import Definitions.Def_ExplicitCost_Cost
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_GroupingRun
import Definitions.Def_Printed_Achievable
import Definitions.Def_QueryMachines_Runs
import Definitions.Def_GeneralPieces_Main
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_GroupingLemma
import Theorems.Thm_PaddedDescent_F_Mark_InvS_size

set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed Sizes

theorem ExplicitCost.answerCall_within (hL : LabelLengthIsL) (hSlow : QueryMachines.StSlowDown) (hSub : QueryMachines.StSubstWithin) {c₁ : ℕ} {α : Type} (E : QueryMachine TableQuery ℤ α ℤ) (arg : CliqueInput → α)
    {a b K g : ℕ} (hK0 : 0 < K) {N : Net g} {P B τ 𝒯 SE x : ℕ} (hb : 0 < b) (hab : a ≤ b) (hN : N.Is P B)
    (hE : SolvesCliques E (arg (unary K, unary (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U), unary (AppRunningTime.B'of K g P B))) K (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) (AppRunningTime.B'of K g P B) 𝒯 SE)
    (hentry : ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * AppRunningTime.Lof K g ((a : ℝ) / b) P N.U),
      entryData.Within (netOracle N) (fun _ => τ) ((dataInput K N P B, x), toLists K (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U) (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁) ((g * (P + B)) ^ c₁)
        ((Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).W γ Θ) ∧
      |(Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).W γ Θ| < 2 ^ bitsOut K g P B) :
    (answerCall E arg).Within (netOracle N) (fun _ => τ) (groupingInput a b K N P B, callOf (groupingInput a b K N P B, x)) (𝒯 * (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁ + 2))
      (size (groupingInput a b K N P B, x) + SE + (g * (P + B)) ^ c₁ + 1) (Value.groupClique asked.under (netInput N P B) N hK0 x (AppRunningTime.Lof K g ((a : ℝ) / b) P N.U)).value := by sorry
