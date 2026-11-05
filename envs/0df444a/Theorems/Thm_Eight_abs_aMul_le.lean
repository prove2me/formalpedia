-- Prove2me | Theorems.Thm_Eight_abs_aMul_le
-- name    : Eight.abs_aMul_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:52:13.106297+00:00
-- url     : https://prove2.me/theorems/30cff48d-3d2a-4f84-bda6-ed1316048c09
-- title:
--   Eight: abs a Mul le
-- statement:
--   The paper's «|A_i| ≤ 2^t», read off the program, for all inputs.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L154-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L154-L154

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

theorem Eight.abs_aMul_le (p : ℕ × FourL) : |aMul p| ≤ 2 ^ tL p.2 := by sorry
