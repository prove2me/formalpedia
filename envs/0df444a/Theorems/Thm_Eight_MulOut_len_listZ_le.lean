-- Prove2me | Theorems.Thm_Eight_MulOut_len_listZ_le
-- name    : Eight.MulOut.len_listZ_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:51:53.038213+00:00
-- url     : https://prove2.me/theorems/d10041fb-49fe-4411-80ce-3b9efd547a65
-- title:
--   Mul Out: len list Z le
-- statement:
--   The word of a list of k integers whose words have length at most b has length at most k·(b + 2) + 2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L157-L163
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L157-L163

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
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open Eight
open Groundwork PaddedDescent.F Finset Polynomial

theorem Eight.MulOut.len_listZ_le (b : ℕ) : ∀ l : List ℤ, (∀ z ∈ l, len z ≤ b) → len l ≤ l.length * (b + 2) + 2
  := by sorry
