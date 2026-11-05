-- Prove2me | Theorems.Thm_Eight_neg_one_pow_add_neg_one_pow
-- name    : Eight.neg_one_pow_add_neg_one_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:41:15.94764+00:00
-- url     : https://prove2.me/theorems/81d2e86d-79bd-4a60-b584-4b9905640ff8
-- title:
--   Eight: neg one pow add neg one pow
-- statement:
--   Why oddness is what «we have to show»: (−1)^m + (−1)^n = 0 if m + n is odd.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L245-L256
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_Identity.lean#L245-L256

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

theorem Eight.neg_one_pow_add_neg_one_pow {m n : ℕ} (h : Odd (m + n)) : (-1 : ℤ) ^ m + (-1) ^ n = 0 := by sorry
