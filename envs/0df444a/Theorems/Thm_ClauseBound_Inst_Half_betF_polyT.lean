-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_betF_polyT
-- name    : ClauseBound.Inst.Half.betF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:12:20.894989+00:00
-- url     : https://prove2.me/theorems/a527f01f-9e13-4f83-9b1b-7bf68d9e9646
-- title:
--   Half: bet F poly T
-- statement:
--   The coefficient of one term of the recursion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L42-L44
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L42-L44

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

theorem ClauseBound.Inst.Half.betF_polyT {W n : α → ℕ} {r : α → ℤ} (hW : Unary W) (hn : PolyT n) (hr : PolyT r) :
    PolyT fun x => betF (W x) (n x) (r x) := by sorry
