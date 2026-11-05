-- Prove2me | Theorems.Thm_Eight_MulOut_blkL_ofFn
-- name    : Eight.MulOut.blkL_ofFn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:26:39.634363+00:00
-- url     : https://prove2.me/theorems/8ad702b3-fd8e-4a1b-a412-9bdc02a02e62
-- title:
--   Mul Out: blk L of Fn
-- statement:
--   The block number s of the list of a string is the block number s of the string.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L53-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L53-L54

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

theorem Eight.MulOut.blkL_ofFn {lam : ℕ} (x : Pieces.Bits lam) (s : ℕ) : blkL (List.ofFn x) s = blockAt x s := by sorry
