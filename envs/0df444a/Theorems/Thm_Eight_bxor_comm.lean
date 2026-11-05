-- Prove2me | Theorems.Thm_Eight_bxor_comm
-- name    : Eight.bxor_comm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:25.212115+00:00
-- url     : https://prove2.me/theorems/22db23f9-2260-45e9-95b0-1609eecb6749
-- title:
--   Eight: bxor comm
-- statement:
--   p ⊕ q = q ⊕ p: the same law in each bit.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L44-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L44-L44

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

theorem Eight.bxor_comm (p q : Block) : bxor p q = bxor q p := by sorry
