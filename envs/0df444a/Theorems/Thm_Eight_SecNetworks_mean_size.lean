-- Prove2me | Theorems.Thm_Eight_SecNetworks_mean_size
-- name    : Eight.SecNetworks.mean_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:53:22.777439+00:00
-- url     : https://prove2.me/theorems/46d80b7d-7e68-411c-951c-f409e9d7e015
-- title:
--   Sec Networks: mean size
-- statement:
--   «A group has mean size g/K».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L266-L268
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L266-L268

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

theorem Eight.SecNetworks.mean_size (γ : Fin K) : (∑ χ : Fin g → Fin K, #{a | χ a = γ}) * K = g * K ^ g := by sorry
