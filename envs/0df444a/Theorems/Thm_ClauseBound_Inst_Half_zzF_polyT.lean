-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_zzF_polyT
-- name    : ClauseBound.Inst.Half.zzF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:40:17.168373+00:00
-- url     : https://prove2.me/theorems/c3b11433-0136-45f5-a1d4-24f4564c964e
-- title:
--   Half: zz F poly T
-- statement:
--   The number z_ν.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L124-L125
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L124-L125

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Inst_HalfTab
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ClauseBound_Inst_CertHalfTab
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Inst ClauseBound.Inst.Half
open Groundwork PaddedDescent.F ClauseBound.Inst.Rec
variable {α : Type} [Enc α]

theorem ClauseBound.Inst.Half.zzF_polyT {ν : α → List ℕ} (hν : PolyT ν) : PolyT fun x => zzF (ν x) := by sorry
