-- Prove2me | Theorems.Thm_ClauseBound_Inst_Rec_powZ_polyT
-- name    : ClauseBound.Inst.Rec.powZ_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:32:13.510817+00:00
-- url     : https://prove2.me/theorems/12a2ff60-603d-4649-937f-f994220fe282
-- title:
--   Rec: pow Z poly T
-- statement:
--   The Rec construction uses the pow Z poly T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L200-L201
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/RecArith.lean#L200-L201

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

theorem ClauseBound.Inst.Rec.powZ_polyT {b : α → ℤ} {k : α → ℕ} (hb : PolyT b) (hk : Unary k) : PolyT fun x => powZ (b x) (k x) := by sorry
