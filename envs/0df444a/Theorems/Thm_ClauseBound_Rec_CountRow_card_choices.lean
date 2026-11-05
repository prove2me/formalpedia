-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_card_choices
-- name    : ClauseBound.Rec.CountRow.card_choices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:37.107696+00:00
-- url     : https://prove2.me/theorems/b9a5507b-4b95-45d4-8710-d1bfa299d2f2
-- title:
--   Count Row: card choices
-- statement:
--   There are 4^n choices of one label on every block.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L138-L139
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L138-L139

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

theorem ClauseBound.Rec.CountRow.card_choices (hh : 1 ≤ h) : Fintype.card (∀ b : Fin (nblk n h), BLab n h b) = 4 ^ n := by sorry
