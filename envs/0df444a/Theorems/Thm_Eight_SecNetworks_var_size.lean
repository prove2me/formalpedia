-- Prove2me | Theorems.Thm_Eight_SecNetworks_var_size
-- name    : Eight.SecNetworks.var_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:54:13.441853+00:00
-- url     : https://prove2.me/theorems/25db41a9-226f-4bd6-accb-dd68d7f701f5
-- title:
--   Sec Networks: var size
-- statement:
--   «and variance at most g/K»: Σ_χ (|G_γ| − g/K)² ≤ (g/K)·K^g, multiplied by K².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L271-L276
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L271-L276

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

theorem Eight.SecNetworks.var_size (γ : Fin K) : ∑ χ : Fin g → Fin K, ((K : ℤ) * (#{a | χ a = γ} : ℕ) - (g : ℤ)) ^ 2 ≤ ((g * K * K ^ g : ℕ) : ℤ) := by sorry
