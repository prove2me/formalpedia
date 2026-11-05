-- Prove2me | Theorems.Thm_ClauseBound_Grid_rowNet_c_le_pd
-- name    : ClauseBound.Grid.rowNet_c_le_pd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:10.790194+00:00
-- url     : https://prove2.me/theorems/f53ab059-7e0a-40c6-90f8-a6ba99733151
-- title:
--   Grid: row Net c le pd
-- statement:
--   Two rows have capacity at most d²·mL if every rectangle is charged at most 2mL bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L135-L137
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L135-L137

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

theorem ClauseBound.Grid.rowNet_c_le_pd {d L m : ℕ} (hm : 1 ≤ m) (hγ : Fintype.card γ = d) (R : Inst (ρ × γ) α) (C : Rect ρ γ → Cut α τ)
    (t₀ : τ) (hcap : ∀ ω, (C ω).cap ≤ 2 * m * L) (a b : ρ) : (rowNet R C t₀ L).c a b ≤ d ^ 2 * (m * L) := by sorry
