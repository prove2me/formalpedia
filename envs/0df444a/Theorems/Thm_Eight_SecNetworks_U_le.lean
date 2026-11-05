-- Prove2me | Theorems.Thm_Eight_SecNetworks_U_le
-- name    : Eight.SecNetworks.U_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:21:03.508817+00:00
-- url     : https://prove2.me/theorems/41a3bf84-85b3-45f6-bbd7-f2b8f87c9529
-- title:
--   Sec Networks: U le
-- statement:
--   «U ≤ |J|·P by (i)» (after Definition 2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L253-L256
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L253-L256

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

theorem Eight.SecNetworks.U_le {g P B : ℕ} {N : Net g} (h : N.Is P B) : N.U ≤ g * P := by sorry
