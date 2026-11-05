-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_stepE_polyT
-- name    : ClauseBound.Inst.Half.stepE_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:40:27.495723+00:00
-- url     : https://prove2.me/theorems/bd2e280b-5730-4887-b396-eae9def41239
-- title:
--   Half: step E poly T
-- statement:
--   One step of a round.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L126-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L126-L128

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfPart
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfPart
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Part Partitions
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.stepE_polyT {k E : α → ℕ} {old new : α → PT} (hk : PolyT k) (ho : PolyT old) (hn : PolyT new) (hE : PolyT E) :
    PolyT fun x => stepE (k x) (old x) (new x) (E x) := by sorry
