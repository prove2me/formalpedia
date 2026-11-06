-- Prove2me | Theorems.Thm_Eight_SecNetworks_mean_Y
-- name    : Eight.SecNetworks.mean_Y
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:52:56.269199+00:00
-- url     : https://prove2.me/theorems/466199d9-7b4a-4997-a66e-9e4ea02b050f
-- title:
--   Sec Networks: mean Y
-- statement:
--   «so 𝔼Y_{γ,γ'} = U/K²».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L120-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L120-L123

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

theorem Eight.SecNetworks.mean_Y (c : Fin g → Fin g → ℕ) {γ γ' : Fin K} (hne : γ ≠ γ') :
    (∑ χ : Fin g → Fin K, Y c χ γ γ') * K ^ 2 = K ^ g * ∑ a, ∑ b ∈ univ.erase a, c a b := by sorry
