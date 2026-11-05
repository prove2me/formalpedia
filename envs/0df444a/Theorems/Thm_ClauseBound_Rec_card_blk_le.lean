-- Prove2me | Theorems.Thm_ClauseBound_Rec_card_blk_le
-- name    : ClauseBound.Rec.card_blk_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:38.66196+00:00
-- url     : https://prove2.me/theorems/6c6d0983-28d0-403a-846b-79398f81353c
-- title:
--   Rec: card blk le
-- statement:
--   A block has at most h positions.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Blocks.lean#L53-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Blocks.lean#L53-L63

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_Blocks
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Rec
open Finset Polynomial Pieces
variable {n h : ℕ}

theorem ClauseBound.Rec.card_blk_le (hh : 1 ≤ h) (b : ℕ) : #(blk n h b) ≤ h := by sorry
