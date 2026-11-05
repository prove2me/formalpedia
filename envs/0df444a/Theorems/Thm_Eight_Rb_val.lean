-- Prove2me | Theorems.Thm_Eight_Rb_val
-- name    : Eight.Rb_val
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:44.136554+00:00
-- url     : https://prove2.me/theorems/1d168d08-c441-46cb-919c-d6e921a7501b
-- title:
--   Eight: Rb val
-- statement:
--   «Both have values in {−1, 0, 1}»: R. This does not need the sign rule.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L124-L129
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L124-L129

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

theorem Eight.Rb_val (x y u v : Block) : Rb x y u v = -1 ∨ Rb x y u v = 0 ∨ Rb x y u v = 1 := by sorry
