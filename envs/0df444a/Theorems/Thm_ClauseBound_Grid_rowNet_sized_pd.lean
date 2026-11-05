-- Prove2me | Theorems.Thm_ClauseBound_Grid_rowNet_sized_pd
-- name    : ClauseBound.Grid.rowNet_sized_pd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:59.686196+00:00
-- url     : https://prove2.me/theorems/22e46964-a42f-462f-892c-d1cd2f1c55c3
-- title:
--   Grid: row Net sized pd
-- statement:
--   The shape and the magnitudes of the row network when every rectangle is charged at most 2mL
--   bits, m ≥ 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L169-L194
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L169-L194

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

theorem ClauseBound.Grid.rowNet_sized_pd {p d L m B b : ℕ} (hm : 1 ≤ m) (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d)
    (hα : Fintype.card α = 2 ^ L) (R : Inst (ρ × γ) α) (hR : ∀ w h, |R w h| ≤ 2 ^ B)
    {G : Rect ρ γ → α → α → α → α → ℤ} (C : Rect ρ γ → Cut α τ) (t₀ : τ)
    (hF : ∀ ω, (C ω).Factors (G ω)) (hcard : ∀ ω, #(C ω).lab ≤ 2 ^ (C ω).cap) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L)
    (htop : ∀ ω x y θ, |(C ω).top x y θ| ≤ 2 ^ b) (hbot : ∀ ω u v θ, |(C ω).bot u v θ| ≤ 2 ^ b)
    (hG : ∀ ω x y u v, |G ω x y u v| ≤ 2 ^ b) :
    (rowNet R C t₀ L).Sized (m * (p * d ^ 2 * L)) (d * B + d ^ 2 * b) := by sorry
