-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_muF_unary
-- name    : ClauseBound.Inst.Rec.muF_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:35:44.900761+00:00
-- url     : https://prove2.me/theorems/6fc0cd22-51cd-485c-9bd2-0fb1eb1aa9b1
-- title:
--   Rec: mu F unary
-- statement:
--   The Rec construction uses the mu F unary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L258-L259
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L258-L259

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

theorem ClauseBound.Inst.Rec.muF_unary {lam h : α → ℕ} (hl : Unary lam) (hh : PolyT h) : Unary fun x => muF (lam x) (h x) := by sorry
