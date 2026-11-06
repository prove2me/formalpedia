-- Prove2me | Theorems.Thm_ExplicitCost_firstGrouping_cast
-- name    : ExplicitCost.firstGrouping_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:27:43.327982+00:00
-- url     : https://prove2.me/theorems/dd1d6129-da2f-4ef9-aa14-b0499b9aa7d5
-- title:
--   Explicit Cost: first Grouping cast
-- statement:
--   **The first grouping that the test accepts**, for ζ = 1/b and a network on n = g nodes in case (i)
--   or (ii).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallLemma.lean#L33-L47
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallLemma.lean#L33-L47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallLemma
import Theorems.Thm_P2M_Groundwork_PolyT_find__e812ffd764ea
attribute [local fun_prop] P2M_Groundwork_PolyT_find__e812ffd764ea


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.firstGrouping_cast (hG : GroupingWithCall) (hL : LabelLengthIsL) {b K g n : ℕ} (hn : n = g) (hK0 : 0 < K) (N : Net n) {P B : ℕ} (hK : 2 ≤ K) (hg : 2 ≤ g) (hb : 1 ≤ b) (hN : N.Is P B)
    (hC : AppRunningTime.Cases K n ((1 : ℝ) / b) P N.c) {x : ℕ} (hx : (List.range (K ^ g)).find? (fun x' => goodData (((1, b), ((unary K, unary g), netInput N P B)), x')) = some x) :
    x < K ^ g ∧ (∀ γ : Fin K, K * #{v : Fin n | Paper.grouping hK0 x v = γ} ≤ 2 * g) ∧
      (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ AppRunningTime.Lof K g ((1 : ℝ) / b) P N.U) ∧
      labelLength ((1, b), ((unary K, unary g), netInput N P B)) = AppRunningTime.Lof K g ((1 : ℝ) / b) P N.U := by sorry
