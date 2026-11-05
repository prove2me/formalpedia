-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_sum_odd
-- name    : ClauseBound.Rec.CountRow.sum_odd
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:45.807073+00:00
-- url     : https://prove2.me/theorems/479679e7-f0d0-4810-a4ef-0315658e02dd
-- title:
--   Count Row: sum odd
-- statement:
--   The sum of odd(β) over all β is 4^n times the mean.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L142-L147
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L142-L147

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Blocks
import Definitions.Def_ClauseBound_Rec_Tail
import Definitions.Def_ClauseBound_Rec_CountRow
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
open ClauseBound.Rec.CountRow
variable {n h : ℕ}

theorem ClauseBound.Rec.CountRow.sum_odd (n : ℕ) (hh : 1 ≤ h) : ((∑ β : Lab n, odd h β : ℕ) : ℝ) = 4 ^ n * mean n h := by sorry
