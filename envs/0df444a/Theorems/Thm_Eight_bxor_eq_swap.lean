-- Prove2me | Theorems.Thm_Eight_bxor_eq_swap
-- name    : Eight.bxor_eq_swap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:22.684965+00:00
-- url     : https://prove2.me/theorems/3639fab0-ef5d-4ba1-a6e2-c985f7dce19b
-- title:
--   Eight: bxor eq swap
-- statement:
--   The two brackets say the same.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L52-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L52-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_Blocks
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.bxor_eq_swap (x y u v : Block) : bxor x y = bxor v u ↔ bxor x u = bxor v y := by sorry
