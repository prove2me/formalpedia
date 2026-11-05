-- Prove2me | Theorems.Thm_Eight_bxor_zero
-- name    : Eight.bxor_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:45:29.407311+00:00
-- url     : https://prove2.me/theorems/f5ecb825-bcab-48a1-b8d7-535468168f9d
-- title:
--   Eight: bxor zero
-- statement:
--   p ⊕ 000 = p: the same law in each bit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L53-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L53-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_EightSquareStatement
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Definitions.Def_Eight_SecCrossing_Identity
set_option autoImplicit false
section
section
open Eight
open Finset

theorem Eight.bxor_zero (p : Block) : bxor p (false, false, false) = p := by sorry
