-- Prove2me | Theorems.Thm_ClauseBound_Rec_mu_eq
-- name    : ClauseBound.Rec.mu_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:38:11.693778+00:00
-- url     : https://prove2.me/theorems/4ff0e65a-4302-4157-98f5-fb028dac095f
-- title:
--   Rec: mu eq
-- statement:
--   μ in closed form: the sum of (2^{n_b} − 1)·2^{h − n_b} over the blocks b, where n_b is the
--   number of positions of b, divided by 2^{h+1} and rounded down.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L233-L240
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L233-L240

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
open CountRow
variable {n h : ℕ}

theorem ClauseBound.Rec.mu_eq (n : ℕ) (hh : 1 ≤ h) :
    mu n h = (∑ b ∈ range (nblk n h), (2 ^ #(blk n h b) - 1) * 2 ^ (h - #(blk n h b))) / 2 ^ (h + 1) := by sorry
