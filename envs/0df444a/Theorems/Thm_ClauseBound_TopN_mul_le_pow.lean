-- Prove2me | Theorems.Thm_ClauseBound_TopN_mul_le_pow
-- name    : ClauseBound.TopN.mul_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:11:02.973642+00:00
-- url     : https://prove2.me/theorems/fe57b693-61c3-4fa1-8f01-f5b3d5411e3d
-- title:
--   Top N: mul le pow
-- statement:
--   A product of numbers below powers of two.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Budget.lean#L25-L26
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Budget.lean#L25-L26

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_PaddedDescent_F_ArithWalk
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Definitions.Def_ClauseBound_TopN_Budget
set_option autoImplicit false
section
open ClauseBound ClauseBound.TopN
open PaddedDescent PaddedDescent.F CountKSatRate
open WidthK (theta bsum leafC)

theorem ClauseBound.TopN.mul_le_pow {x y p q : ℕ} (hx : x ≤ 2 ^ p) (hy : y ≤ 2 ^ q) : x * y ≤ 2 ^ (p + q) := by sorry
