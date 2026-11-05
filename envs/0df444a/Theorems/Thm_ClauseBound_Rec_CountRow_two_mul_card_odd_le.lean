-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_two_mul_card_odd_le
-- name    : ClauseBound.Rec.CountRow.two_mul_card_odd_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:28.293042+00:00
-- url     : https://prove2.me/theorems/ce23ab81-389b-4f0f-bc58-e8bb7de0f92c
-- title:
--   Count Row: two mul card odd le
-- statement:
--   Twice the number of labels with an odd number of entries 11 is at most the number of all labels.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L100-L102
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L100-L102

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

theorem ClauseBound.Rec.CountRow.two_mul_card_odd_le (ι : Type) [Fintype ι] [DecidableEq ι] :
    2 * #{γ : ι → Bool × Bool | Odd #{k | γ k = (true, true)}} ≤ Fintype.card (ι → Bool × Bool) := by sorry
