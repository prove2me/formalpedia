-- Prove2me | Theorems.Thm_Eight_bxor_right_cancel
-- name    : Eight.bxor_right_cancel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:27.019515+00:00
-- url     : https://prove2.me/theorems/76002530-70a0-468c-82ad-dd27b3ceaf25
-- title:
--   Eight: bxor right cancel
-- statement:
--   «If it holds and y = u, then x = v»: x ⊕ y = v ⊕ y only if x = v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L56-L60
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L56-L60

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

theorem Eight.bxor_right_cancel {x v y : Block} (h : bxor x y = bxor v y) : x = v := by sorry
