-- Prove2me | Theorems.Thm_Eight_abs_getD_mulUpTo_le_choose
-- name    : Eight.abs_getD_mulUpTo_le_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:51:45.145352+00:00
-- url     : https://prove2.me/theorems/f862de32-ed79-4659-a113-2a7a91b3bb20
-- title:
--   Eight: abs get D mul Up To le choose
-- statement:
--   After n factors the entry number j is at most C(n, j) in absolute value, by Pascal's rule. At n =
--   t this is the paper's «|A_i| ≤ C(t, i)».
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L122-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L122-L147

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

theorem Eight.abs_getD_mulUpTo_le_choose (q : FourL) (n j : ℕ) : |(mulUpTo q n).getD j 0| ≤ (n.choose j : ℤ) := by sorry
