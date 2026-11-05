-- Prove2me | Theorems.Thm_Eight_getD_mulStep
-- name    : Eight.getD_mulStep
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:14:04.556352+00:00
-- url     : https://prove2.me/theorems/91a66283-ed06-43f0-888f-337e5d688ce3
-- title:
--   Eight: get D mul Step
-- statement:
--   The entry number j after one multiplication is r·l_j + c·l_{j−1}, also beyond the end of the
--   list, where all three entries count as 0.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L64-L70
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/networks/Eight/SecCrossing_MulOut.lean#L64-L70

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

theorem Eight.getD_mulStep (r c : ℤ) (l : List ℤ) (j : ℕ) : (mulStep r c l).getD j 0 = r * l.getD j 0 + c * (0 :: l).getD j 0 := by sorry
