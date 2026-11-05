-- Prove2me | Theorems.Thm_Eight_len_mulUpTo_le
-- name    : Eight.len_mulUpTo_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:52:09.197731+00:00
-- url     : https://prove2.me/theorems/4fcb3857-a500-47eb-b64e-cba90c7d63a5
-- title:
--   Eight: len mul Up To le
-- statement:
--   The word of the list after n factors has length at most (n + 1)(3n + 10) + 2: the list has n + 1
--   entries, and each is an integer of at most n + 1 binary digits whose word has at most 3n + 8 bits.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L179-L184
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L179-L184

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

theorem Eight.len_mulUpTo_le (q : FourL) (n : ℕ) : len (mulUpTo q n) ≤ (n + 1) * (3 * n + 10) + 2 := by sorry
