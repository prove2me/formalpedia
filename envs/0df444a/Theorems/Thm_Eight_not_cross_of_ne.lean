-- Prove2me | Theorems.Thm_Eight_not_cross_of_ne
-- name    : Eight.not_cross_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:29.608337+00:00
-- url     : https://prove2.me/theorems/c54a7210-117e-4830-8510-bd13f39c3852
-- title:
--   Eight: not cross of ne
-- statement:
--   «If this fails, all three functions are 0»: [x = v][y = u].
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L94-L94
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L94-L94

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

theorem Eight.not_cross_of_ne {x y u v : Block} (h : bxor x y ≠ bxor v u) : ¬(x = v ∧ y = u) := by sorry
