-- Prove2me | Theorems.Thm_Eight_SecNetworks_Net_sized_toPaperNetwork
-- name    : Eight.SecNetworks.Net.sized_toPaperNetwork
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:22:28.585059+00:00
-- url     : https://prove2.me/theorems/f2eda832-58c2-40eb-a61f-3f6d0da88685
-- title:
--   Net: sized to Paper Network
-- statement:
--   The network of proof/networks/Paper satisfies the size conditions of proof/networks/Paper with
--   the same P and B: |S_a| ≤ 2^P, c symmetric, (i), 2^{c_{a,b}} strings θ, and all values at most 2^B
--   in absolute value («below 2^B» gives «at most 2^B»).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L146-L171
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L146-L171

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

theorem Eight.SecNetworks.Net.sized_toPaperNetwork (h : N.Is P B) : N.toPaperNetwork.Sized P B := by sorry
