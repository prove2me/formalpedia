-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_topF_polyT
-- name    : ClauseBound.Inst.Half.topF_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:24:49.572746+00:00
-- url     : https://prove2.me/theorems/f08d345a-814c-4cfb-bc4e-e59b38d1cd52
-- title:
--   Half: top F poly T
-- statement:
--   The function on top of a factorization is polynomial-time; W and h are given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L140-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L140-L152

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

theorem ClauseBound.Inst.Half.topF_polyT {pad : α → U} {W h i : α → ℕ} {flat : α → List (List ℕ)} {μ π σ : α → List ℕ} {r : α → ℤ} (hp : PolyT pad) (hW : Unary W)
    (hf : PolyT flat) (hh : Unary h) (hμ : PolyT μ) (hi : PolyT i) (hr : PolyT r) (hπ : PolyT π) (hσ : PolyT σ) :
    PolyT fun x => topF (pad x) (W x) (flat x) (h x) (μ x) (i x) (r x) (π x) (σ x) := by sorry
