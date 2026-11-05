-- Prove2me | Theorems.Thm_Eight_abs_A_le_choose
-- name    : Eight.abs_A_le_choose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:42:14.429196+00:00
-- url     : https://prove2.me/theorems/c55568b9-aa7d-4289-9e31-948c0e6249ff
-- title:
--   Eight: abs A le choose
-- statement:
--   «|A_i| ≤ C(t,i)»: each of the C(t,i) products in `A_eq_sum_subsets` is −1, 0 or 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L132-L143
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_PiecesAC.lean#L132-L143

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Eight_SecCrossing_Blocks
import Mathlib.Tactic
import Definitions.Def_Eight_SecCrossing_PiecesAC
set_option autoImplicit false
section
section
open Eight
open Finset Polynomial

theorem Eight.abs_A_le_choose (lam i : ℕ) (x y u v : Pieces.Bits lam) : |A lam i x y u v| ≤ ((tOf lam).choose i : ℤ) := by sorry
