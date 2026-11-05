-- Prove2me | Theorems.Thm_Eight_MulOut_len_int_le
-- name    : Eight.MulOut.len_int_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:51:50.806104+00:00
-- url     : https://prove2.me/theorems/43c5617b-8991-4449-8525-b797c7622f40
-- title:
--   Mul Out: len int le
-- statement:
--   The word of an integer of absolute value at most 2^n has length at most 3n + 8.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L166-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L166-L175

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_PolyDefs
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_Eight_SecCrossing_MulOut
set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F Finset Polynomial

theorem Eight.MulOut.len_int_le {z : ℤ} {n : ℕ} (h : |z| ≤ 2 ^ n) : len z ≤ 3 * n + 8 := by sorry
