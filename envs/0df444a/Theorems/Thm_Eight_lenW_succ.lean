-- Prove2me | Theorems.Thm_Eight_lenW_succ
-- name    : Eight.lenW_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:09:27.214266+00:00
-- url     : https://prove2.me/theorems/b7dd9e65-0447-4ff3-b081-a666f4bbf716
-- title:
--   Eight: len W succ
-- statement:
--   One more block makes θ' longer by 6 bits if the block is wide, by 3 bits if not.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L99-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Chunk.lean#L99-L102

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_FactDefs
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Chunk
set_option autoImplicit false
section
section
open Eight
open Groundwork Groundwork.Prog PaddedDescent.F Finset

theorem Eight.lenW_succ (tr : Bool) (Q : List Bool) (t : ℕ) : lenW tr Q (t + 1) = lenW tr Q t + if wide tr Q t = true then 6 else 3 := by sorry
