-- Prove2me | Theorems.Thm_Eight_SecNetworks_size_bits
-- name    : Eight.SecNetworks.size_bits
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:23:46.241465+00:00
-- url     : https://prove2.me/theorems/6460b1e7-8295-45e5-86e8-a119e1fd3197
-- title:
--   Sec Networks: size bits
-- statement:
--   The size of a bit string of length n is 2n + 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L74-L79
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecNetworks_LemGrouping.lean#L74-L79

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecNetworks_Defs
import Definitions.Def_SingleBitPieces_SecNetworks_LemGrouping
import Definitions.Def_ToTuring_Poly_Comb
import Mathlib.Tactic
import Definitions.Def_Eight_SecNetworks_LemGrouping
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight Eight.SecNetworks
open Groundwork Groundwork.Prog Finset Stepped

theorem Eight.SecNetworks.size_bits (w : List Bool) : size w = 2 * w.length + 1 := by sorry
