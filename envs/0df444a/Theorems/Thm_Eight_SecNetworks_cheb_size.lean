-- Prove2me | Theorems.Thm_Eight_SecNetworks_cheb_size
-- name    : Eight.SecNetworks.cheb_size
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T20:00:11.4522+00:00
-- url     : https://prove2.me/theorems/438c7234-02ba-4d93-8623-ce0b76bcd51a
-- title:
--   Sec Networks: cheb size
-- statement:
--   «so it exceeds 2g/K with probability at most K/g», for every g: Chebyshev with deviation g/K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L279-L289
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L279-L289

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

theorem Eight.SecNetworks.cheb_size (γ : Fin K) : g * #{χ : Fin g → Fin K | 2 * g < K * #{a | χ a = γ}} ≤ K * K ^ g := by sorry
