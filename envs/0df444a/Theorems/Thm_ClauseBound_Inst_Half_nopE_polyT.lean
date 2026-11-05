-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_nopE_polyT
-- name    : ClauseBound.Inst.Half.nopE_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:15:25.733166+00:00
-- url     : https://prove2.me/theorems/ad45533a-cf5e-4fbb-a19a-d365eb212a27
-- title:
--   Half: nop E poly T
-- statement:
--   One entry of the normally ordered product with a family given by its table.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L60-L63
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L60-L63

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

theorem ClauseBound.Inst.Half.nopE_polyT {W n : α → ℕ} {flat : α → List (List ℕ)} {T : α → List ℤ} {π σ : α → List ℕ} (hW : Unary W) (hn : PolyT n)
    (hf : PolyT flat) (hT : PolyT T) (hπ : PolyT π) (hσ : PolyT σ) :
    PolyT fun x => nopE (W x) (n x) (flat x) (T x) (π x) (σ x) := by sorry
