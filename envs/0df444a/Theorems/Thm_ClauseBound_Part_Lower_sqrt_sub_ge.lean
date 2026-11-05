-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_sqrt_sub_ge
-- name    : ClauseBound.Part.Lower.sqrt_sub_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:27.833195+00:00
-- url     : https://prove2.me/theorems/3a941cf2-f606-417a-afbc-9bdd130461a9
-- title:
--   Lower: sqrt sub ge
-- statement:
--   √(1 − y) ≥ 1 − y/2 − y²/2 on [0, 1], scaled: √(N − x) ≥ √N − x/(2√N) − x²/(2N√N) for 0 ≤ x ≤ N.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L43-L62
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L43-L62

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower

theorem ClauseBound.Part.Lower.sqrt_sub_ge {s x : ℝ} (hs : 0 < s) (hx : 0 ≤ x) (hxs : x ≤ s ^ 2) :
    s - x / (2 * s) - x ^ 2 / (2 * s ^ 3) ≤ Real.sqrt (s ^ 2 - x) := by sorry
