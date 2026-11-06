-- Prove2me | Theorems.Thm_ExplicitCost_groupClique_value
-- name    : ExplicitCost.groupClique_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:27:37.657886+00:00
-- url     : https://prove2.me/theorems/1256271c-3315-47c0-9e0c-7efe4cb84703
-- title:
--   Explicit Cost: group Clique value
-- statement:
--   «… the (K, L)-clique with the tables W̃_γ, whose value is that of the network», for the clique
--   of the groups as the statements of Lemma 8 name it.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallLemma.lean#L63-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/CountedRecursion/CallLemma.lean#L63-L65

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

theorem ExplicitCost.groupClique_value (hV : ValueIsKept) {K n : ℕ} (hK0 : 0 < K) (N : Net n) {P B : ℕ} (hN : N.Is P B) (x L : ℕ) (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) :
    (Value.groupClique asked.under (netInput N P B) N hK0 x L).value = N.value := by sorry
