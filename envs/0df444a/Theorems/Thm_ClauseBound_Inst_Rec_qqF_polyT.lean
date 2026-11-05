-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_qqF_polyT
-- name    : ClauseBound.Inst.Rec.qqF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:34:17.294224+00:00
-- url     : https://prove2.me/theorems/08e06425-056f-474a-9893-f7828e2c73f0
-- title:
--   Rec: qq F poly T
-- statement:
--   The Rec construction uses the qq F poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L222-L225
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L222-L225

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

theorem ClauseBound.Inst.Rec.qqF_polyT {μ t j : α → ℕ} (hμ : PolyT μ) (ht : Unary t) (hj : PolyT j) :
    PolyT fun x => qqF (μ x) (t x) (j x) := by sorry
