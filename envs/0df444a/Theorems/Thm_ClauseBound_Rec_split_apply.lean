-- Prove2me | Theorems.Thm_ClauseBound_Rec_split_apply
-- name    : ClauseBound.Rec.split_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:12.106896+00:00
-- url     : https://prove2.me/theorems/550b5b13-1ceb-4ce2-8337-0c2879e13d7a
-- title:
--   Rec: split apply
-- statement:
--   The part of β in block b has the entries of β.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Blocks.lean#L84-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Blocks.lean#L84-L87

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

theorem ClauseBound.Rec.split_apply (hh : 1 ≤ h) (β : Lab n) (b : Fin (nblk n h)) (k : {k : Fin n // k.val / h = b.val}) :
    split hh β b k = β k.1 := by sorry
