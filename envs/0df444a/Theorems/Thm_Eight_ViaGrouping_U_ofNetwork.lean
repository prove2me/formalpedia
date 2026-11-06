-- Prove2me | Theorems.Thm_Eight_ViaGrouping_U_ofNetwork
-- name    : Eight.ViaGrouping.U_ofNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:04:29.299263+00:00
-- url     : https://prove2.me/theorems/96246c2f-c978-41a1-8777-c105cc674c58
-- title:
--   Via Grouping: U of Network
-- statement:
--   The total U is the same.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L41-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L41-L41

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_ViaGrouping_Defs
import Mathlib.Tactic
import Definitions.Def_Eight_ViaGrouping_Bridge
set_option autoImplicit false
section
section
open Eight Eight.ViaGrouping
open Groundwork Groundwork.Prog Finset Stepped Eight.SecNetworks
variable {g : ℕ}

theorem Eight.ViaGrouping.U_ofNetwork (N : Paper.Network (Fin g) (List Bool) (List Bool)) (n : Fin g → ℕ) : (ofNetwork N n).U = N.U := by sorry
