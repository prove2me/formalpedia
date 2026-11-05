-- Prove2me | Theorems.Thm_Eight_MulOut_tL_le_len
-- name    : Eight.MulOut.tL_le_len
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:52:12.17391+00:00
-- url     : https://prove2.me/theorems/f10df033-4a21-4390-85ae-e103d876cd29
-- title:
--   Mul Out: t L le len
-- statement:
--   The number of blocks is at most the length of the word of the four strings.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L187-L191
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L187-L191

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

theorem Eight.MulOut.tL_le_len (q : FourL) : tL q ≤ len q := by sorry
