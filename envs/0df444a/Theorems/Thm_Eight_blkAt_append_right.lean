-- Prove2me | Theorems.Thm_Eight_blkAt_append_right
-- name    : Eight.blkAt_append_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:14:09.067993+00:00
-- url     : https://prove2.me/theorems/f46086b4-2112-4bca-953d-f6c1afaeece5
-- title:
--   Eight: blk At append right
-- statement:
--   The three bits from position |u| + j on of u ++ v are those of v from position j on.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L60-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L60-L63

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

theorem Eight.blkAt_append_right (u v : List Bool) (j : ℕ) : blkAt (u ++ v) (u.length + j) = blkAt v j := by sorry
