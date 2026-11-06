-- Prove2me | Theorems.Thm_Eight_SecNetworks_cheb_Y
-- name    : Eight.SecNetworks.cheb_Y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:11:08.018451+00:00
-- url     : https://prove2.me/theorems/332242b3-511e-434c-a624-589364f7ad2f
-- title:
--   Sec Networks: cheb Y
-- statement:
--   «and by Chebyshev Pr(Y_{γ,γ'} > U/K² + gP/K³) ≤ 4K⁶/g», for every g. The event is multiplied by
--   K³. Proved from `var_Y` and `total_le`: the deviation is gP/K³, so the bound is 4gP²·K⁶/(gP)².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L175-L200
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L175-L200

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

theorem Eight.SecNetworks.cheb_Y {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) {γ γ' : Fin K} (hne : γ ≠ γ') :
    g * #{χ : Fin g → Fin K | K * (∑ a, ∑ b ∈ univ.erase a, c a b) + g * P < K ^ 3 * Y c χ γ γ'} ≤ 4 * K ^ 6 * K ^ g := by sorry
