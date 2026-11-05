-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_card_lab
-- name    : ClauseBound.Rec.CountRow.card_lab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:34.382045+00:00
-- url     : https://prove2.me/theorems/b37ee929-1cf8-4373-ab2e-d8b14c87ee89
-- title:
--   Count Row: card lab
-- statement:
--   There are 4^n labels.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L134-L135
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L134-L135

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

theorem ClauseBound.Rec.CountRow.card_lab (n : ℕ) : Fintype.card (Lab n) = 4 ^ n := by sorry
