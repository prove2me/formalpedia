-- Prove2me | Theorems.Thm_Eight_SecNetworks_pair_prob
-- name    : Eight.SecNetworks.pair_prob
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T20:53:27.896281+00:00
-- url     : https://prove2.me/theorems/516db37b-3543-4bd4-b411-7f052d562c30
-- title:
--   Sec Networks: pair prob
-- statement:
--   «Each ordered pair (a,b) contributes with probability 1/K²».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L116-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_Grouping.lean#L116-L117

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

theorem Eight.SecNetworks.pair_prob {a b : Fin g} (hab : a ≠ b) (γ γ' : Fin K) : #{χ : Fin g → Fin K | χ a = γ ∧ χ b = γ'} * K ^ 2 = K ^ g := by sorry
