-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_linF_polyT
-- name    : ClauseBound.Inst.Rec.linF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:33:32.027686+00:00
-- url     : https://prove2.me/theorems/f95e36b7-c932-49bb-abc0-192bff0d2d09
-- title:
--   Rec: lin F poly T
-- statement:
--   The Rec construction uses the lin F poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L227-L234
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L227-L234

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

theorem ClauseBound.Inst.Rec.linF_polyT {a σ : α → ℤ} {w ν z n₀ r : α → ℕ} {ε : α → Bool} (ha : PolyT a) (hw : Unary w) (hσ : PolyT σ) (hν : PolyT ν)
    (hz : Unary z) (hn : Unary n₀) (hε : PolyT ε) (hr : Unary r) :
    PolyT fun x => linF (a x) (w x) (σ x) (ν x) (z x) (n₀ x) (ε x) (r x) := by sorry
