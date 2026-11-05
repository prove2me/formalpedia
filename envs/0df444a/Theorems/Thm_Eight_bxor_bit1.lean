-- Prove2me | Theorems.Thm_Eight_bxor_bit1
-- name    : Eight.bxor_bit1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:22.810883+00:00
-- url     : https://prove2.me/theorems/32c934a1-0c5d-45e3-8984-ac4c26534397
-- title:
--   Eight: bxor bit1
-- statement:
--   The three bits of p ⊕ q (by definition).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L39-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L39-L39

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

theorem Eight.bxor_bit1 (p q : Block) : (bxor p q).1 = (p.1 ^^ q.1) := by sorry
