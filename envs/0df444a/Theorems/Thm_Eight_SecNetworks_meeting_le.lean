-- Prove2me | Theorems.Thm_Eight_SecNetworks_meeting_le
-- name    : Eight.SecNetworks.meeting_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:53:03.881529+00:00
-- url     : https://prove2.me/theorems/9d92af4d-bcab-4580-8db6-2035542d623a
-- title:
--   Sec Networks: meeting le
-- statement:
--   «by (i) the ordered pairs that meet a fixed pair have c-values summing to at most 4P».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L133-L146
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L133-L146

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

theorem Eight.SecNetworks.meeting_le {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) {P : ℕ} (hP : ∀ a, ∑ b ∈ univ.erase a, c a b ≤ P) (p : Fin g × Fin g) :
    ∑ q : Fin g × Fin g with q.1 ≠ q.2 ∧ (q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2), c q.1 q.2 ≤ 4 * P := by sorry
