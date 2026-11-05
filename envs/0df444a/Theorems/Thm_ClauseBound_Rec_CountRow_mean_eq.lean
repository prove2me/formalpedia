-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_mean_eq
-- name    : ClauseBound.Rec.CountRow.mean_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:36.768724+00:00
-- url     : https://prove2.me/theorems/cf621359-93f8-4b47-abd7-91cc2079676f
-- title:
--   Count Row: mean eq
-- statement:
--   The mean with the denominator 2^{h+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L214-L217
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L214-L217

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

theorem ClauseBound.Rec.CountRow.mean_eq (n : ℕ) (hh : 1 ≤ h) :
    mean n h = ((∑ b ∈ range (nblk n h), (2 ^ #(blk n h b) - 1) * 2 ^ (h - #(blk n h b)) : ℕ) : ℝ) / ((2 ^ (h + 1) : ℕ) : ℝ) := by sorry
