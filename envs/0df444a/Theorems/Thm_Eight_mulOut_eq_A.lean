-- Prove2me | Theorems.Thm_Eight_mulOut_eq_A
-- name    : Eight.mulOut_eq_A
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:51:15.999249+00:00
-- url     : https://prove2.me/theorems/a105ff15-b66d-4498-8ce7-bd719d857d89
-- title:
--   Eight: mul Out eq A
-- statement:
--   On four strings of λ bits, written as lists, the entry number i of mulOut is A_i, for every λ
--   and every i (for i > t both are 0). Same as in the paper: A_i is the coefficient of T^i in the
--   product of the t factors.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L97-L101
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L97-L101

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

theorem Eight.mulOut_eq_A (lam i : ℕ) (x y u v : Pieces.Bits lam) : (mulOut (List.ofFn x, List.ofFn y, List.ofFn u, List.ofFn v)).getD i 0 = A lam i x y u v := by sorry
