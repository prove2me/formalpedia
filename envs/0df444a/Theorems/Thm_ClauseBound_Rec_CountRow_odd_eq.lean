-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_odd_eq
-- name    : ClauseBound.Rec.CountRow.odd_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:22.788167+00:00
-- url     : https://prove2.me/theorems/14c6783a-344d-4985-9e2e-c3af3d7356e3
-- title:
--   Count Row: odd eq
-- statement:
--   odd(β) is the number of blocks in which the part of β is marked.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L127-L131
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L127-L131

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

theorem ClauseBound.Rec.CountRow.odd_eq (hh : 1 ≤ h) (β : Lab n) : odd h β = #{b | split hh β b ∈ oddSet n h b} := by sorry
