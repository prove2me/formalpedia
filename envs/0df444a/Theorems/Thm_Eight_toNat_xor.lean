-- Prove2me | Theorems.Thm_Eight_toNat_xor
-- name    : Eight.toNat_xor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:36:41.02464+00:00
-- url     : https://prove2.me/theorems/474545fc-fd6e-4b78-82f8-12940d02763c
-- title:
--   Eight: to Nat xor
-- statement:
--   «and compute modulo 2»: on bits, a ⊕ b ≡ a + b. (The definition of ⊕ on a bit: the four values
--   of (a,b).)
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L84-L84
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L84-L84

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

theorem Eight.toNat_xor (a b : Bool) : (a ^^ b).toNat ≡ a.toNat + b.toNat [MOD 2] := by sorry
