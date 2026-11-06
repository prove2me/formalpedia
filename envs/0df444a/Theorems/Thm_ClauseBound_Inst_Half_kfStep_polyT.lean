-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_kfStep_polyT
-- name    : ClauseBound.Inst.Half.kfStep_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:38:13.641439+00:00
-- url     : https://prove2.me/theorems/48f7cfaf-8ce4-4f44-b4a1-3b9e78a503a2
-- title:
--   Half: kf Step poly T
-- statement:
--   One round: the tables for one more factor.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L102-L112
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L102-L112

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

theorem ClauseBound.Inst.Half.kfStep_polyT {W h n : α → ℕ} {flat : α → List (List ℕ)} {S : α → List (List ℤ)} (hW : Unary W) (hh : Unary h) (hn : PolyT n)
    (hf : PolyT flat) (hS : PolyT S) : PolyT fun x => kfStep (W x) (h x) (n x) (flat x) (S x) := by sorry
