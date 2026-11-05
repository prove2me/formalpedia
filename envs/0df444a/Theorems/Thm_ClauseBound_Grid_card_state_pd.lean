-- Prove2me | Theorems.Thm_ClauseBound_Grid_card_state_pd
-- name    : ClauseBound.Grid.card_state_pd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:39:51.329103+00:00
-- url     : https://prove2.me/theorems/e836823f-012f-4df2-ac21-e013fea62bb7
-- title:
--   Grid: card state pd
-- statement:
--   A row has d nodes with pd half-edges each, so its states are the strings of p·d²·L bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L107-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Grid/Size.lean#L107-L111

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

theorem ClauseBound.Grid.card_state_pd {p d L : ℕ} (hρ : Fintype.card ρ = p) (hγ : Fintype.card γ = d) (hα : Fintype.card α = 2 ^ L) :
    Fintype.card (RowSt ρ γ α) = 2 ^ (p * d ^ 2 * L) := by sorry
