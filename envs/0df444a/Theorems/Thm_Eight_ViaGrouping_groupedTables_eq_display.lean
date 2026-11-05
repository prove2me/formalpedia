-- Prove2me | Theorems.Thm_Eight_ViaGrouping_groupedTables_eq_display
-- name    : Eight.ViaGrouping.groupedTables_eq_display
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:34:26.917984+00:00
-- url     : https://prove2.me/theorems/66ff6807-9d4d-41b8-8ea2-94b92325a1ed
-- title:
--   Via Grouping: grouped Tables eq display
-- statement:
--   The tables of `StTable` and `StValue` are the display, for Θ : [K] ∖ {γ} → {0,1}^L and Y_{γ,γ'}
--   ≤ L. This is `SecNetworks.tables_eq`, for procedures that need not give B.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Display.lean#L50-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Display.lean#L50-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Table
import Definitions.Def_Eight_SecNetworks_Tables
import Definitions.Def_Eight_SecNetworks_Clique
import Definitions.Def_Eight_ViaGrouping_Display
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Groundwork.Prog.NetE Finset Stepped Eight.SecNetworks
variable {C : Type} [HasSize C] {g K : ℕ}
variable {Np : Procs C} {c : C} {N : Net g} {P B τ S : ℕ}

theorem Eight.ViaGrouping.groupedTables_eq_display (h : IsNetworkP Np c N P B τ S) (hK0 : 0 < K) (x L : ℕ) (hL : ∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L)
    (γ : Fin K) (Θ : Fin K → List Bool) (hΘ : ∀ γ', γ' ≠ γ → (Θ γ').length = L) :
    Paper.groupedTables Np.toPaperNetwork c N.toPaperNetwork hK0 x L γ Θ = display Np c N hK0 x γ Θ := by sorry
