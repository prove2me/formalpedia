-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_initT_polyT
-- name    : ClauseBound.Inst.Half.initT_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T21:40:31.710098+00:00
-- url     : https://prove2.me/theorems/2d816dfd-dbbc-4f9f-8961-9b9a3bb1b69e
-- title:
--   Half: init T poly T
-- statement:
--   The table before the first round.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L118-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfPart.lean#L118-L123

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

theorem ClauseBound.Inst.Half.initT_polyT {W : α → ℕ} (hW : Unary W) : PolyT fun x => initT (W x) := by sorry
