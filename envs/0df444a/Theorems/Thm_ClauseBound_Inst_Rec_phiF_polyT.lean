-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_phiF_polyT
-- name    : ClauseBound.Inst.Rec.phiF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:34:13.352866+00:00
-- url     : https://prove2.me/theorems/0c581105-aa6d-4a92-aad4-636481d2804a
-- title:
--   Rec: phi F poly T
-- statement:
--   The Rec construction uses the phi F poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L217-L220
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L217-L220

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

theorem ClauseBound.Inst.Rec.phiF_polyT {a j : α → ℤ} {w : α → ℕ} (ha : PolyT a) (hw : Unary w) (hj : PolyT j) :
    PolyT fun x => phiF (a x) (w x) (j x) := by sorry
