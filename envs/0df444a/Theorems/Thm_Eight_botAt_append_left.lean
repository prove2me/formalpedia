-- Prove2me | Theorems.Thm_Eight_botAt_append_left
-- name    : Eight.botAt_append_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:53:21.104763+00:00
-- url     : https://prove2.me/theorems/0d47961e-2097-4bf7-aa5a-369744cdea81
-- title:
--   Eight: bot At append left
-- statement:
--   The same for the second function.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L123-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L123-L131

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

theorem Eight.botAt_append_left (tr : Bool) (Q a b : List Bool) {u : List Bool} (v : List Bool) {s t : ℕ} (hs : s < t) (hu : u.length = lenW tr Q t) :
    botAt tr Q (u ++ v) a b s = botAt tr Q u a b s := by sorry
