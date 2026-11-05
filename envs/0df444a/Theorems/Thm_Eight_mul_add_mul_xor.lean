-- Prove2me | Theorems.Thm_Eight_mul_add_mul_xor
-- name    : Eight.mul_add_mul_xor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:40:43.179007+00:00
-- url     : https://prove2.me/theorems/a26683bf-9f2c-4de3-b3e4-102c22a77b5d
-- title:
--   Eight: mul add mul xor
-- statement:
--   For one bit: c·a + c·(a ⊕ b) ≡ c·a + c·(a + b) = 2·c·a + c·b ≡ c·b (modulo 2).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L100-L105
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L100-L105

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

theorem Eight.mul_add_mul_xor (c : ℕ) (a b : Bool) : c * a.toNat + c * (a ^^ b).toNat ≡ c * b.toNat [MOD 2] := by sorry
