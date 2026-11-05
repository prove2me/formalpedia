-- Prove2me | Theorems.Thm_Eight_blkAt_append_left
-- name    : Eight.blkAt_append_left
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:27:15.976726+00:00
-- url     : https://prove2.me/theorems/b7279b7f-cc54-463b-8a14-e959f462aec1
-- title:
--   Eight: blk At append left
-- statement:
--   The three bits from position j on of u ++ v are those of u, if they lie inside u.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L55-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L55-L57

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

theorem Eight.blkAt_append_left {u : List Bool} (v : List Bool) {j : ℕ} (h : j + 3 ≤ u.length) : blkAt (u ++ v) j = blkAt u j := by sorry
