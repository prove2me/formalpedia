-- Prove2me | Theorems.Thm_ClauseBound_Grid_U_rowNet_pd
-- name    : ClauseBound.Grid.U_rowNet_pd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:11.08794+00:00
-- url     : https://prove2.me/theorems/9529b28b-5a88-4cd6-b35b-81f119059a84
-- title:
--   Grid: U row Net pd
-- statement:
--   The total U of the row network: it counts ordered pairs of rows, so every vertical edge and
--   every rectangle counts twice.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L198-L208
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L198-L208

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

theorem ClauseBound.Grid.U_rowNet_pd {p d L : ℕ} (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d) (R : Inst (ρ × γ) α)
    (C : Rect ρ γ → Cut α τ) (t₀ : τ) :
    (rowNet R C t₀ L).U = p * (p - 1) * d * L + 2 * ∑ ω ∈ Ω ρ γ, (C ω).cap := by sorry
