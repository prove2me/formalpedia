-- Prove2me | Theorems.Thm_Eight_SecNetworks_some_group
-- name    : Eight.SecNetworks.some_group
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:11:10.690554+00:00
-- url     : https://prove2.me/theorems/6f57cda2-5695-4876-be1a-801780a135a3
-- title:
--   Sec Networks: some group
-- statement:
--   «by a union bound over the K groups, some group does so with probability at most K²/g», for
--   every g.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L293-L301
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L293-L301

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

theorem Eight.SecNetworks.some_group : g * #{χ : Fin g → Fin K | ∃ γ, 2 * g < K * #{a | χ a = γ}} ≤ K ^ 2 * K ^ g := by sorry
