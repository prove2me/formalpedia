-- Prove2me | Theorems.Thm_Eight_getD_mulUpTo
-- name    : Eight.getD_mulUpTo
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:50:55.662366+00:00
-- url     : https://prove2.me/theorems/2ceba791-2294-4a2f-8a41-9bba883ab1a9
-- title:
--   Eight: get D mul Up To
-- statement:
--   After n factors the entry number i is the coefficient of T^i in the product of the first n
--   factors.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L80-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L80-L92

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

theorem Eight.getD_mulUpTo (q : FourL) (n i : ℕ) : (mulUpTo q n).getD i 0 = (∏ s ∈ range n, (C (rAt q s) + X * C (cAt q s))).coeff i := by sorry
