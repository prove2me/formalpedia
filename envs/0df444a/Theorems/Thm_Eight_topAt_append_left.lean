-- Prove2me | Theorems.Thm_Eight_topAt_append_left
-- name    : Eight.topAt_append_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:52:11.544332+00:00
-- url     : https://prove2.me/theorems/fa484ae4-2a1b-4514-afee-fbd54b789747
-- title:
--   Eight: top At append left
-- statement:
--   The factor of the block number s < t in the first function reads only the part of θ' that
--   belongs to the first t blocks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L112-L120
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L112-L120

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Chunk
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset

theorem Eight.topAt_append_left (tr : Bool) (Q a b : List Bool) {u : List Bool} (v : List Bool) {s t : ℕ} (hs : s < t) (hu : u.length = lenW tr Q t) :
    topAt tr Q (u ++ v) a b s = topAt tr Q u a b s := by sorry
