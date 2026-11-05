-- Prove2me | Theorems.Thm_Eight_mulUpTo_succ
-- name    : Eight.mulUpTo_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:27:14.054787+00:00
-- url     : https://prove2.me/theorems/33f3d444-3590-40ee-9199-2e98e8c9f784
-- title:
--   Eight: mul Up To succ
-- statement:
--   The factor number n is multiplied in after the factors number 0, …, n − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L73-L74
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L73-L74

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

theorem Eight.mulUpTo_succ (q : FourL) (n : ℕ) : mulUpTo q (n + 1) = mulStep (rAt q n) (cAt q n) (mulUpTo q n) := by sorry
