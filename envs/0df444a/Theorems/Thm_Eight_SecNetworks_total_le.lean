-- Prove2me | Theorems.Thm_Eight_SecNetworks_total_le
-- name    : Eight.SecNetworks.total_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:11:38.247268+00:00
-- url     : https://prove2.me/theorems/731b65e0-9c69-48a3-aadf-8883919a1e08
-- title:
--   Sec Networks: total le
-- statement:
--   «4PU ≤ 4gP²»: U ≤ gP, by (i).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L169-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L169-L171

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

theorem Eight.SecNetworks.total_le {c : Fin g → Fin g → ℕ} {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) : ∑ a, ∑ b ∈ univ.erase a, c a b ≤ g * P := by sorry
