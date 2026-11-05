-- Prove2me | Theorems.Thm_ClauseBound_Rec_two_mul_mu_le
-- name    : ClauseBound.Rec.two_mul_mu_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:37:52.400673+00:00
-- url     : https://prove2.me/theorems/98734747-f5fa-48f2-8f6f-78f97c56141b
-- title:
--   Rec: two mul mu le
-- statement:
--   2μ ≤ δ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L226-L229
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L226-L229

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

theorem ClauseBound.Rec.two_mul_mu_le (n : ℕ) (hh : 1 ≤ h) : 2 * mu n h ≤ nblk n h := by sorry
