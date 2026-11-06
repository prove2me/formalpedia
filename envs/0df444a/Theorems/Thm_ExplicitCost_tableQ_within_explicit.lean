-- Prove2me | Theorems.Thm_ExplicitCost_tableQ_within_explicit
-- name    : ExplicitCost.tableQ_within_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:22:55.37821+00:00
-- url     : https://prove2.me/theorems/12109cfa-5512-444c-8736-73755677b74a
-- title:
--   Explicit Cost: table Q within explicit
-- statement:
--   **The machine of Lemma 1 for K and g, with explicit numbers**: an entry costs at most
--   2^{P⌊2g/K⌋}·(8g² + 1)·τ operations.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean#L55-L76
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean#L55-L76

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ExplicitCost_EntryDefs
import Definitions.Def_ExplicitCost_SameRuns
import Definitions.Def_Printed_GroupingEntry
import Definitions.Def_Printed_Close
import Definitions.Def_Printed_Coding
import Definitions.Def_QueryMachines_Runs
import Mathlib.Tactic
import Definitions.Def_ExplicitCost_Cost
set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.tableQ_within_explicit {K g : ℕ} (hK0 : 0 < K) (N : Net g) {P B τ : ℕ} (hN : N.Is P B) (hτ : 1 ≤ τ) (x L : ℕ)
    (hG1 : ∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) (γ : Fin K) {Θ : List Bool} (hΘ : Θ ∈ words ((K - 1) * L)) :
    (tableQ K g asked).Within (netOracle N) (fun _ => τ) ((netInput N P B, x), toLists K L (γ.val, Θ)) (2 ^ (P * (2 * g / K)) * (g * g * 8 + 1) * τ)
      (size (netInput N P B) + 2 * size g + 4 * P + B + 4 + 4 * (size (netInput N P B) + size x + size K + K * (2 * L + 2)) + 5 * (P * (2 * g / K)) + 2 * (B * (g * g)) + 3 * size (g * g) + 30)
      ((Value.groupClique asked.under (netInput N P B) N hK0 x L).W γ Θ) := by sorry
