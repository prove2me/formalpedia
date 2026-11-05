-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_share_eq
-- name    : ClauseBound.Rec.CountRow.share_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:45.689348+00:00
-- url     : https://prove2.me/theorems/3221b5d5-43ac-43f7-822f-1c669e586779
-- title:
--   Count Row: share eq
-- statement:
--   The share of the marked labels on a block of N ≤ h positions is (1 − 2^{−N})/2, written with the
--   denominator 2^{h+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L177-L211
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L177-L211

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

theorem ClauseBound.Rec.CountRow.share_eq (hh : 1 ≤ h) (b : Fin (nblk n h)) :
    (#(oddSet n h b) : ℝ) / Fintype.card (BLab n h b)
      = (((2 ^ #(blk n h b.val) - 1) * 2 ^ (h - #(blk n h b.val)) : ℕ) : ℝ) / ((2 ^ (h + 1) : ℕ) : ℝ) := by sorry
