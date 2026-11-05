-- Prove2me | Theorems.Thm_Eight_ViaGrouping_tableM_display
-- name    : Eight.ViaGrouping.tableM_display
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:09:21.28951+00:00
-- url     : https://prove2.me/theorems/2e212d4f-05a0-45ec-b412-45be6c760061
-- title:
--   Via Grouping: table M display
-- statement:
--   **The procedure `tableM` computes the display.** For a grouping with (G1) and Y_{γ,γ'} ≤ L ≤
--   2gP, and every query (γ, Θ) with L bits for every other group and the empty string at γ: `tableM`
--   returns the display of W̃_γ(Θ) within c₁·2^{P·⌊2g/K⌋}·τ steps, on states of size at most
--   S + c₁·(size c + P + B)^{c₁}, and the display is at most 2^{P·⌊2g/K⌋ + g²B} in absolute value. The
--   constant depends on K and g only.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Display.lean#L60-L68
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Display.lean#L60-L68

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

theorem Eight.ViaGrouping.tableM_display (K g : ℕ) : ∃ c₁ : ℕ, 1 ≤ c₁ ∧ ∀ (hK0 : 0 < K) (C : Type) [HasSize C] (Np : Procs C) (c : C) (N : Net g) (P B τ S : ℕ), IsNetworkP Np c N P B τ S →
    ∀ x < K ^ g, ∀ L ≤ 2 * (g * P), (∀ γ : Fin K, K * #{a : Fin g | Paper.grouping hK0 x a = γ} ≤ 2 * g) → (∀ γ γ' : Fin K, γ ≠ γ' → Y N.c (Paper.grouping hK0 x) γ γ' ≤ L) →
    ∀ (γ : Fin K) (Θ : Fin K → List Bool), (∀ γ', γ' ≠ γ → (Θ γ').length = L) → Θ γ = [] →
      (tableM K g Np).Runs ((c, x), γ.1, List.ofFn Θ) (c₁ * 2 ^ (P * (2 * g / K)) * τ) (S + c₁ * (size c + P + B) ^ c₁) (display Np c N hK0 x γ Θ) ∧
        |display Np c N hK0 x γ Θ| ≤ 2 ^ (P * (2 * g / K) + g ^ 2 * B) := by sorry
