-- Prove2me | Theorems.Thm_Eight_MulOut_getD_ofFn
-- name    : Eight.MulOut.getD_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:56:08.551362+00:00
-- url     : https://prove2.me/theorems/ddd05d61-843d-485e-85b2-08aea0adcb94
-- title:
--   Mul Out: get D of Fn
-- statement:
--   A position of the list of a string holds the bit of the string, and 0 beyond the end («Append 3t
--   − λ zeros to each of x, y, u, v»).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L47-L50
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L47-L50

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

theorem Eight.MulOut.getD_ofFn {lam : ℕ} (x : Pieces.Bits lam) (j : ℕ) : (List.ofFn x).getD j false = bitAt x j := by sorry
