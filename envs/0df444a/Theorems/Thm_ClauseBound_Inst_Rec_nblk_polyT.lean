-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_nblk_polyT
-- name    : ClauseBound.Inst.Rec.nblk_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:34:09.323491+00:00
-- url     : https://prove2.me/theorems/1060113e-3c55-432e-9b87-b0ea3a3af6bf
-- title:
--   Rec: nblk poly T
-- statement:
--   The Rec construction uses the nblk poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L242-L243
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L242-L243

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec
variable {α β : Type} [Enc α] [Enc β]

theorem ClauseBound.Inst.Rec.nblk_polyT {lam h : α → ℕ} (hl : PolyT lam) (hh : PolyT h) : PolyT fun x => Pieces.nblk (lam x) (h x) := by sorry
