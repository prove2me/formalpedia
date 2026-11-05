-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_map_range_polyT
-- name    : ClauseBound.Inst.Rec.map_range_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:46:59.328139+00:00
-- url     : https://prove2.me/theorems/a5c35268-4184-4796-841f-fc43c65c550f
-- title:
--   Rec: map range poly T
-- statement:
--   The Rec construction uses the map range poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L189-L193
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L189-L193

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Data
import Definitions.Def_ClauseBound_Rec_Defs
import Definitions.Def_ClauseBound_Rec_CountRow
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_RecArith
import Theorems.Thm_Groundwork_PolyT_map
attribute [local fun_prop] Groundwork.PolyT.map


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Rec
open Finset Polynomial Groundwork PaddedDescent.F ClauseBound.Rec
variable {α β : Type} [Enc α] [Enc β]

theorem ClauseBound.Inst.Rec.map_range_polyT {w : α → ℕ} {f : α → ℕ → β} (hw : Unary w) (hf : PolyT fun p : α × ℕ => f p.1 (min p.2 (w p.1))) :
    PolyT fun x => (List.range (w x)).map (f x) := by sorry
