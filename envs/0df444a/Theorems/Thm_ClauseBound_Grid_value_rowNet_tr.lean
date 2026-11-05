-- Prove2me | Theorems.Thm_ClauseBound_Grid_value_rowNet_tr
-- name    : ClauseBound.Grid.value_rowNet_tr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:19.135126+00:00
-- url     : https://prove2.me/theorems/7f3e6952-0a71-4009-92a9-4fac2f758cef
-- title:
--   Grid: value row Net tr
-- statement:
--   The column network: if the cuts factor the functions of the transposed grid, the row network of
--   the transposed grid has the value of the grid itself.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Expand.lean#L63-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Expand.lean#L63-L66

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Groundwork_Grid_Expand
import Definitions.Def_ClauseBound_Grid_Expand
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Grid
open Finset Groundwork Groundwork.Grid
variable {ρ γ α τ : Type}
variable [Fintype ρ] [LinearOrder ρ] [Fintype γ] [LinearOrder γ] [Fintype α] [DecidableEq α]

theorem ClauseBound.Grid.value_rowNet_tr {G : Rect ρ γ → α → α → α → α → ℤ} {C : Rect γ ρ → Cut α τ} (h : ∀ ω, (C ω).Factors (trG G ω))
    (R : Inst (ρ × γ) α) (t₀ : τ) (L : ℕ) : (rowNet (trInst R) C t₀ L).value = ZG R G := by sorry
