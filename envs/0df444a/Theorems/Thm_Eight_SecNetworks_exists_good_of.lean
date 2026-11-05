-- Prove2me | Theorems.Thm_Eight_SecNetworks_exists_good_of
-- name    : Eight.SecNetworks.exists_good_of
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:10:55.344661+00:00
-- url     : https://prove2.me/theorems/d5d1e86d-e887-495f-a475-933fbb6637e1
-- title:
--   Sec Networks: exists good of
-- statement:
--   «By a union bound over these two events, the grouping fails to be good with probability less
--   than 1, so a good grouping exists.» From «less than 2/3» and «less than 1/3».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L307-L320
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L307-L320

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Groundwork_Net_Colouring
import Definitions.Def_Eight_SecNetworks_Grouping
import Theorems.Thm_Groundwork_PolyT_all
attribute [local fun_prop] Groundwork.PolyT.all


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Finset Groundwork.Colouring
variable {g K : ℕ}

theorem Eight.SecNetworks.exists_good_of {c : Fin g → Fin g → ℕ} {P : ℕ}
    (h1 : 3 * #{χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ g)
    (h2 : 3 * #{χ : Fin g → Fin K | ∃ γ, 2 * g < K * #{a | χ a = γ}} < K ^ g) : ∃ χ : Fin g → Fin K, Good c P χ := by sorry
