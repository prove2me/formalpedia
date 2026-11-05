-- Prove2me | Theorems.Thm_Eight_SecNetworks_Net_lab_toPaperNetwork
-- name    : Eight.SecNetworks.Net.lab_toPaperNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:20:25.555204+00:00
-- url     : https://prove2.me/theorems/ce5825da-25c0-45f6-802f-0fdf8add28c4
-- title:
--   Net: lab to Paper Network
-- statement:
--   In the network of proof/networks/Paper, θ ranges over {0,1}^{c_{a,b}} for the pair {a, b}, in
--   either order.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L102-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L102-L105

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

theorem Eight.SecNetworks.Net.lab_toPaperNetwork (h : N.Is P B) (a b : Fin g) : N.toPaperNetwork.lab a b = words (N.c a b) := by sorry
