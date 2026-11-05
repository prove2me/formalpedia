-- Prove2me | Theorems.Thm_Eight_MulOut_abs_rAt_le
-- name    : Eight.MulOut.abs_rAt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:51:11.059545+00:00
-- url     : https://prove2.me/theorems/6d26bd51-6edf-48a8-87ea-cad16b2225c7
-- title:
--   Mul Out: abs r At le
-- statement:
--   «coefficients in {−1, 0, 1}»: |R| ≤ 1 at every block.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L115-L115
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L115-L115

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

theorem Eight.MulOut.abs_rAt_le (q : FourL) (s : ℕ) : |rAt q s| ≤ 1 := by sorry
