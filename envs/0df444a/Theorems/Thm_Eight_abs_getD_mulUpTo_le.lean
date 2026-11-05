-- Prove2me | Theorems.Thm_Eight_abs_getD_mulUpTo_le
-- name    : Eight.abs_getD_mulUpTo_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:13:54.498168+00:00
-- url     : https://prove2.me/theorems/37a5e554-37f0-48b4-b31e-a96c05ab0e25
-- title:
--   Eight: abs get D mul Up To le
-- statement:
--   After n factors every entry is at most 2^n in absolute value.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L150-L151
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L150-L151

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

theorem Eight.abs_getD_mulUpTo_le (q : FourL) (n j : ℕ) : |(mulUpTo q n).getD j 0| ≤ 2 ^ n := by sorry
