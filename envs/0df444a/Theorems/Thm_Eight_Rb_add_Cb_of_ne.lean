-- Prove2me | Theorems.Thm_Eight_Rb_add_Cb_of_ne
-- name    : Eight.Rb_add_Cb_of_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:40.487232+00:00
-- url     : https://prove2.me/theorems/64688f6d-ea16-4a2e-a658-7fbe82499653
-- title:
--   Eight: Rb add Cb of ne
-- statement:
--   «If it holds and y ≠ u, then R + C = 0 by the sign rule with (p,q,p',q') = (x,y,v,u)».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L107-L109
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L107-L109

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

theorem Eight.Rb_add_Cb_of_ne (hS : Signs) {x y u v : Block} (h : bxor x y = bxor v u) (hyu : y ≠ u) : Rb x y u v + Cb x y u v = 0 := by sorry
