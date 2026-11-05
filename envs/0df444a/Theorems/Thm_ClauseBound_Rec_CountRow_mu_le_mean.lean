-- Prove2me | Theorems.Thm_ClauseBound_Rec_CountRow_mu_le_mean
-- name    : ClauseBound.Rec.CountRow.mu_le_mean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:01:43.458797+00:00
-- url     : https://prove2.me/theorems/26fa4703-aff1-4442-993a-9c4b039611aa
-- title:
--   Count Row: mu le mean
-- statement:
--   μ is at most the mean.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L150-L154
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Rec/CountRow.lean#L150-L154

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

theorem ClauseBound.Rec.CountRow.mu_le_mean (n : ℕ) (hh : 1 ≤ h) : (mu n h : ℝ) ≤ mean n h := by sorry
