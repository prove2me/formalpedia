-- Prove2me | Theorems.Thm_ClauseBound_TopN_add_le_pow
-- name    : ClauseBound.TopN.add_le_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:34:33.684754+00:00
-- url     : https://prove2.me/theorems/4f18f7d7-e1c0-4a66-93db-57f80a7c77cf
-- title:
--   Top N: add le pow
-- statement:
--   A sum of two numbers below powers of two.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Budget.lean#L29-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Budget.lean#L29-L34

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

theorem ClauseBound.TopN.add_le_pow {x y p q r : ℕ} (hx : x ≤ 2 ^ p) (hy : y ≤ 2 ^ q) (hp : p < r) (hq : q < r) : x + y ≤ 2 ^ r := by sorry
