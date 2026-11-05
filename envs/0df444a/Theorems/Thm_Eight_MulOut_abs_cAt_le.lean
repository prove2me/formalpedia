-- Prove2me | Theorems.Thm_Eight_MulOut_abs_cAt_le
-- name    : Eight.MulOut.abs_cAt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:51:54.404436+00:00
-- url     : https://prove2.me/theorems/a8c5caa5-f39e-4a06-80a1-7b475fac1e09
-- title:
--   Mul Out: abs c At le
-- statement:
--   «coefficients in {−1, 0, 1}»: |C| ≤ 1 at every block.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L118-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L118-L118

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

theorem Eight.MulOut.abs_cAt_le (q : FourL) (s : ℕ) : |cAt q s| ≤ 1 := by sorry
