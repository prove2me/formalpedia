-- Prove2me | Theorems.Thm_ExplicitCost_entryCost_cast
-- name    : ExplicitCost.entryCost_cast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:24:46.913616+00:00
-- url     : https://prove2.me/theorems/1bc87ad4-a967-4f4b-a5de-ea6c63ea4b38
-- title:
--   Explicit Cost: entry Cost cast
-- statement:
--   **The cost of an entry, with one constant**, for a network on n = g nodes.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallLemma.lean#L50-L59
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallLemma.lean#L50-L59

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CountedRecursion_CallParts
import Definitions.Def_Printed_GroupingEntry
import Mathlib.Tactic
import Definitions.Def_CountedRecursion_CallLemma
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Groundwork.Grid PaddedDescent.F ClauseBound.Alg ClauseBound.Alg.GridNet Eight Eight.SecNetworks Eight.Level Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.entryCost_cast (hE : EntryCostExplicit) : ∃ c₁ : ℕ, ∀ (K g n : ℕ) (_ : n = g) (hK0 : 0 < K) (N : Net n) (P B τ : ℕ), K ≤ g → N.Is P B → 1 ≤ τ →
    ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin n | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
      ∀ (γ : Fin K), ∀ Θ ∈ words ((K - 1) * L),
        entryData.Within (netOracle N) (fun _ => τ) ((((unary K, unary g), netInput N P B), x), toLists K L (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * τ * (g * (P + B)) ^ c₁) ((g * (P + B)) ^ c₁)
          ((Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ) ∧
        |(Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ| < 2 ^ bitsOut K g P B := by sorry
