-- Prove2me | Theorems.Thm_Eight_ViaGrouping_value_ofNetwork
-- name    : Eight.ViaGrouping.value_ofNetwork
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:04:28.644733+00:00
-- url     : https://prove2.me/theorems/b495bc87-a298-4958-94c3-5efed7e33c29
-- title:
--   Via Grouping: value of Network
-- statement:
--   The value is the same: both are Σ_z ∏_a W_a(z_a) ∏_{a<b} Ψ_{a,b}(z_a, z_b) with the same S, W,
--   Ψ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L38-L38
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/ViaGrouping/Bridge.lean#L38-L38

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

theorem Eight.ViaGrouping.value_ofNetwork (N : Paper.Network (Fin g) (List Bool) (List Bool)) (n : Fin g → ℕ) : (ofNetwork N n).value = N.value := by sorry
