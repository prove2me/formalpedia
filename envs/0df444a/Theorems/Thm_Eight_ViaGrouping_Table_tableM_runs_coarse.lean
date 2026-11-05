-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_tableM_runs_coarse
-- name    : Eight.ViaGrouping.Table.tableM_runs_coarse
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:14.604526+00:00
-- url     : https://prove2.me/theorems/2eb704a2-04d1-496a-aefe-a40a2cd7db7a
-- title:
--   Table: table M runs coarse
-- statement:
--   The bounds of `tableM_runs` with one constant c₁ that depends on K and g only: «one entry costs
--   2^{2gP/K}·poly(P + B)·τ operations». For a grouping whose groups have at most m ≤ 2g nodes, with
--   Y_{γ,γ'} ≤ β ≤ 2gP: at most c₁·2^{Pm}·τ steps on states of size at most
--   S + c₁·(size c + P + B)^{c₁}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L383-L427
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L383-L427

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Table
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
open Eight.ViaGrouping.Table
variable {C : Type} [HasSize C] {K g : ℕ} {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}
variable {x β : ℕ} {G : Fin K} {θ : Fin K → List Bool}

theorem Eight.ViaGrouping.Table.tableM_runs_coarse (K g : ℕ) : ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
    ∀ x < K ^ g, ∀ β ≤ 2 * (g * P), ∀ m ≤ 2 * g, (∀ G < K, (members K g x G).length ≤ m) → (∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β) →
    ∀ (G : Fin K) (θ : Fin K → List Bool), (∀ G', G' ≠ G → (θ G').length = β) → θ G = [] →
    (tableM K g Np).Runs ((c, x), (G.val, List.ofFn θ)) (c₁ * 2 ^ (P * m) * τ) (S + c₁ * (size c + P + B) ^ c₁) (mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ))) := by sorry
