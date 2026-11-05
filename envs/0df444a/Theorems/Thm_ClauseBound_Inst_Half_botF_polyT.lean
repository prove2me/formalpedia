-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_botF_polyT
-- name    : ClauseBound.Inst.Half.botF_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:24:52.411253+00:00
-- url     : https://prove2.me/theorems/f3f8b4ca-058c-4371-9511-4bdd0193c758
-- title:
--   Half: bot F poly T
-- statement:
--   The function below of a factorization is polynomial-time; W and h are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L155-L161
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L155-L161

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

theorem ClauseBound.Inst.Half.botF_polyT {pad : α → U} {W h : α → ℕ} {flat : α → List (List ℕ)} {μ π σ : α → List ℕ} {r : α → ℤ} (hp : PolyT pad) (hW : Unary W)
    (hf : PolyT flat) (hh : Unary h) (hμ : PolyT μ) (hr : PolyT r) (hπ : PolyT π) (hσ : PolyT σ) :
    PolyT fun x => botF (pad x) (W x) (flat x) (h x) (μ x) (r x) (π x) (σ x) := by sorry
