-- Prove2me | Theorems.Thm_ClauseBound_Rec_card_BLab
-- name    : ClauseBound.Rec.card_BLab
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:17.352509+00:00
-- url     : https://prove2.me/theorems/109457bd-7fb6-4c1a-856b-3c43a30ea9ee
-- title:
--   Rec: card BLab
-- statement:
--   Block b has 4^{n_b} labels.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Blocks.lean#L90-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Blocks.lean#L90-L92

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

theorem ClauseBound.Rec.card_BLab (b : Fin (nblk n h)) : Fintype.card (BLab n h b) = 4 ^ #(blk n h b.val) := by sorry
