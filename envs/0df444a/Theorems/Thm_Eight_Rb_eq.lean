-- Prove2me | Theorems.Thm_Eight_Rb_eq
-- name    : Eight.Rb_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:39:44.012226+00:00
-- url     : https://prove2.me/theorems/2dad4996-d369-400b-a9b3-3a78928a49ed
-- title:
--   Eight: Rb eq
-- statement:
--   «Indeed, R = [x ⊕ y = v ⊕ u]σ(x,y)σ(v,u)».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L75-L75
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L75-L75

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

theorem Eight.Rb_eq (x y u v : Block) : Rb x y u v = if bxor x y = bxor v u then sigma x y * sigma v u else 0 := by sorry
