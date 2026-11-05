-- Prove2me | Theorems.Thm_ClauseBound_Grid_card_labels_le
-- name    : ClauseBound.Grid.card_labels_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:56.134402+00:00
-- url     : https://prove2.me/theorems/13d4d5e6-ebc9-4a7c-8096-64564a9aba71
-- title:
--   Grid: card labels le
-- statement:
--   The number of labels of two rows.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L115-L121
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L115-L121

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Size
import Definitions.Def_ClauseBound_Grid_Size
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]
omit [DecidableEq α]

theorem ClauseBound.Grid.card_labels_le {d L : ℕ} (hγ : Fintype.card γ = d) (hα : Fintype.card α = 2 ^ L)
    (S : γ × γ → Finset τ) (e : γ × γ → ℕ) (h : ∀ k, #(S k) ≤ 2 ^ e k) (t₀ : τ) :
    #((univ : Finset (γ → α)) ×ˢ tuples (fun k : γ × γ => k.1 < k.2) S t₀) ≤
      2 ^ (d * L + ∑ k : γ × γ with k.1 < k.2, e k) := by sorry
