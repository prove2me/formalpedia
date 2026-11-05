-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_nbF_unary
-- name    : ClauseBound.Inst.Rec.nbF_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:36:16.067202+00:00
-- url     : https://prove2.me/theorems/df906434-a4ba-4b14-902a-f022f5dbb437
-- title:
--   Rec: nb F unary
-- statement:
--   The Rec construction uses the nb F unary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L251-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L251-L252

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

theorem ClauseBound.Inst.Rec.nbF_unary {lam h b : α → ℕ} (hl : Unary lam) (hh : PolyT h) (hb : PolyT b) : Unary fun x => nbF (lam x) (h x) (b x) := by sorry
