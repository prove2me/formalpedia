-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_mean_le
-- name    : ClauseBound.Rec.CountRow.mean_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:33.466845+00:00
-- url     : https://prove2.me/theorems/de4116d9-a240-4a76-a5ae-d75c76026573
-- title:
--   Count Row: mean le
-- statement:
--   The mean is at most δ/2.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L165-L173
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L165-L173

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

theorem ClauseBound.Rec.CountRow.mean_le (n h : ℕ) : mean n h ≤ (nblk n h : ℝ) / 2 := by sorry
