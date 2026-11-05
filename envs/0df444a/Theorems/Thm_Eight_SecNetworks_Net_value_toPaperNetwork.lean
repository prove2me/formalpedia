-- Prove2me | Theorems.Thm_Eight_SecNetworks_Net_value_toPaperNetwork
-- name    : Eight.SecNetworks.Net.value_toPaperNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:33:38.468316+00:00
-- url     : https://prove2.me/theorems/efe4bef6-5e83-48bc-b1fd-ae16ab09396d
-- title:
--   Net: value to Paper Network
-- statement:
--   The value Z is the same: a choice z with some z_a outside S_a contributes 0, since W_a is 0
--   there, and the other choices contribute what they contribute in N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L128-L141
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L128-L141

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_LemGrouping
set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset Stepped
open Eight.SecNetworks.Net
variable {g : ℕ} (N : Net g)
variable {N} {P B : ℕ}

theorem Eight.SecNetworks.Net.value_toPaperNetwork (h : N.Is P B) : N.toPaperNetwork.value = N.value := by sorry
