-- Prove2me | Theorems.Thm_ExplicitCost_mergedVal_eq_display
-- name    : ExplicitCost.mergedVal_eq_display
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T06:24:07.696291+00:00
-- url     : https://prove2.me/theorems/ede8fb38-7e55-44a3-926b-e27ea5281447
-- title:
--   Explicit Cost: merged Val eq display
-- statement:
--   The integer that the step machine for an entry returns is the display of W̃_γ(Θ).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean#L45-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ExplicitCost/Cost.lean#L45-L48

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ExplicitCost
open Finset Groundwork Groundwork.Prog Groundwork.Prog.NetE Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed

theorem ExplicitCost.mergedVal_eq_display {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ} (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ)
    (hY : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) (γ : Fin K) (θ : Fin K → List Bool) (hθ : ∀ γ', γ' ≠ γ → (θ γ').length = L) :
    mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (γ.val, List.ofFn θ)) = display Np c N hK0 x γ θ := by sorry
