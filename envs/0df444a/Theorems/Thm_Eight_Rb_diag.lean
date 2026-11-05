-- Prove2me | Theorems.Thm_Eight_Rb_diag
-- name    : Eight.Rb_diag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:39.283253+00:00
-- url     : https://prove2.me/theorems/8a83ba8a-748b-4d36-96d2-5bc6e94475e8
-- title:
--   Eight: Rb diag
-- statement:
--   «If it holds and y = u, then x = v and R = C = σ(x,y)² = 1»: here with x = v and y = u put in.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L97-L97
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L97-L97

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

theorem Eight.Rb_diag (x y : Block) : Rb x y y x = 1 := by sorry
