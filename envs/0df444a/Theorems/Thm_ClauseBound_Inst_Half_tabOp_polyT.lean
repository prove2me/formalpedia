-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_tabOp_polyT
-- name    : ClauseBound.Inst.Half.tabOp_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:19:21.41146+00:00
-- url     : https://prove2.me/theorems/95b4f263-b569-4a37-968d-d3c43d03a89b
-- title:
--   Half: tab Op poly T
-- statement:
--   The table of a[·], built part by part and cut off by the pad after every round.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L73-L78
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L73-L78

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

theorem ClauseBound.Inst.Half.tabOp_polyT {pad : α → U} {W : α → ℕ} {flat : α → List (List ℕ)} {a : α → List ℕ} (hp : PolyT pad) (hW : Unary W)
    (hf : PolyT flat) (ha : PolyT a) : PolyT fun x => tabOp (pad x) (W x) (flat x) (a x) := by sorry
