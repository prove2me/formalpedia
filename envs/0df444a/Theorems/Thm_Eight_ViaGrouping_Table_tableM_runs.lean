-- Prove2me | Theorems.Thm_Eight_ViaGrouping_Table_tableM_runs
-- name    : Eight.ViaGrouping.Table.tableM_runs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:20:31.670906+00:00
-- url     : https://prove2.me/theorems/62725d1b-f17c-4cc8-9861-5191edaec25f
-- title:
--   Table: table M runs
-- statement:
--   «The sum defining W̃_γ(Θ) has at most (2^P)^{2g/K} terms, each a product of at most g² values …
--   and one entry costs 2^{2gP/K}·poly(P + B)·τ operations», with explicit numbers: if every group has
--   at most m nodes and Y_{γ,γ'} ≤ β, then `tableM` answers a well-formed
--   query (β bits for every other group) within 2^{Pm}·(g²(4τ + 4) + 1) steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L310-L358
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Table.lean#L310-L358

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

theorem Eight.ViaGrouping.Table.tableM_runs (h : IsNetworkP Np c N P B τ S) (m : ℕ) (hm : ∀ G < K, (members K g x G).length ≤ m)
    (hβ : ∀ G < K, ∀ G' < K, G ≠ G' → lbLen K g Np.toPaperNetwork c x G G' ≤ β) (hθ : ∀ G', G' ≠ G → (θ G').length = β) (hG : θ G = []) :
    (tableM K g Np).Runs ((c, x), (G.val, List.ofFn θ)) (2 ^ (P * m) * (g * g * (4 * τ + 4) + 1))
      (S + 4 * (size c + size x + size K + K * (2 * β + 2)) + 5 * (P * m) + 2 * (B * (g * g)) + 3 * size (g * g) + 30)
      (mergedVal K g Np.toPaperNetwork N.toPaperNetwork ((c, x), (G.val, List.ofFn θ))) := by sorry
