-- Prove2me | Theorems.Thm_Eight_Cb_eq
-- name    : Eight.Cb_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:02:33.609086+00:00
-- url     : https://prove2.me/theorems/aaa117df-1345-4277-930b-0fbb3d462c53
-- title:
--   Eight: Cb eq
-- statement:
--   «and C = [x ⊕ u = v ⊕ y]σ(x,u)σ(v,y)».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L78-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Blocks.lean#L78-L78

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

theorem Eight.Cb_eq (x y u v : Block) : Cb x y u v = if bxor x u = bxor v y then sigma x u * sigma v y else 0 := by sorry
