-- Prove2me | Theorems.Thm_Eight_Rb_of_ne
-- name    : Eight.Rb_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:37.230967+00:00
-- url     : https://prove2.me/theorems/4b6c69f3-a95b-44ff-bcdc-8d0cc03a228e
-- title:
--   Eight: Rb of ne
-- statement:
--   «If this fails, all three functions are 0»: R.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L87-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L87-L87

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

theorem Eight.Rb_of_ne {x y u v : Block} (h : bxor x y ≠ bxor v u) : Rb x y u v = 0 := by sorry
