-- Prove2me | Theorems.Thm_Eight_SecNetworks_some_pair
-- name    : Eight.SecNetworks.some_pair
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:53:19.482194+00:00
-- url     : https://prove2.me/theorems/b06ff412-812d-4dd4-865c-1b0dfd9aa6bf
-- title:
--   Sec Networks: some pair
-- statement:
--   «By a union bound over the fewer than K²/2 pairs of groups, some pair violates this bound with
--   probability less than» (K²/2)·(4K⁶/g), for every g: the union runs over the pairs γ < γ' only, since
--   Y_{γ,γ'} = Y_{γ',γ}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L236-L261
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L236-L261

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

theorem Eight.SecNetworks.some_pair (hK : 1 ≤ K) {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) :
    g * #{χ : Fin g → Fin K | ∃ γ γ', γ ≠ γ' ∧ K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} < 2 * K ^ 8 * K ^ g := by sorry
