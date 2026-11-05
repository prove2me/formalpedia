-- Prove2me | Theorems.Thm_ClauseBound_Rec_nblk_le
-- name    : ClauseBound.Rec.nblk_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:31.536144+00:00
-- url     : https://prove2.me/theorems/3db15709-e159-4202-a229-11867a585a94
-- title:
--   Rec: nblk le
-- statement:
--   There are at most n blocks.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Blocks.lean#L31-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/Blocks.lean#L31-L35

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

theorem ClauseBound.Rec.nblk_le (n : ℕ) (hh : 1 ≤ h) : nblk n h ≤ n := by sorry
