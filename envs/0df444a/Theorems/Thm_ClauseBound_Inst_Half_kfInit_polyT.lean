-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_kfInit_polyT
-- name    : ClauseBound.Inst.Half.kfInit_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:32:04.98645+00:00
-- url     : https://prove2.me/theorems/afb93a4e-39a1-4a44-a3cf-81c856686ad6
-- title:
--   Half: kf Init poly T
-- statement:
--   The tables before the first round.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L83-L87
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L83-L87

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

theorem ClauseBound.Inst.Half.kfInit_polyT {h : α → ℕ} {flat : α → List (List ℕ)} (hh : Unary h) (hf : PolyT flat) :
    PolyT fun x => kfInit (h x) (flat x) := by sorry
