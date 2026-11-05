-- Prove2me | Theorems.Thm_Eight_SecNetworks_Y_symm
-- name    : Eight.SecNetworks.Y_symm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:10:46.968629+00:00
-- url     : https://prove2.me/theorems/1edc9e78-3458-4aa3-bec3-b7eb4c611a00
-- title:
--   Sec Networks: Y symm
-- statement:
--   «let Y_{γ,γ'} = Y_{γ',γ} be the sum of c_{a,b} over all a ∈ G_γ and b ∈ G_{γ'}»: the equality,
--   from c_{a,b} = c_{b,a}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L110-L113
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L110-L113

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

theorem Eight.SecNetworks.Y_symm {c : Fin g → Fin g → ℕ} (hs : ∀ a b, c a b = c b a) (χ : Fin g → Fin K) (γ γ' : Fin K) : Y c χ γ γ' = Y c χ γ' γ := by sorry
