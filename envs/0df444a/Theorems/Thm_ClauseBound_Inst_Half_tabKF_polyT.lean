-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_tabKF_polyT
-- name    : ClauseBound.Inst.Half.tabKF_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T23:40:26.279208+00:00
-- url     : https://prove2.me/theorems/fa05e9bb-053c-4925-9052-4ea40e87fb74
-- title:
--   Half: tab KF poly T
-- statement:
--   The tables of the parts of weight 0, …, h of a^μ, cut off by the pad after every round.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L115-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L115-L119

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

theorem ClauseBound.Inst.Half.tabKF_polyT {pad : α → U} {W h : α → ℕ} {flat : α → List (List ℕ)} {μ : α → List ℕ} (hp : PolyT pad) (hW : Unary W)
    (hf : PolyT flat) (hh : Unary h) (hμ : PolyT μ) : PolyT fun x => tabKF (pad x) (W x) (flat x) (h x) (μ x) := by sorry
