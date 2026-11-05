-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_lookT_polyT
-- name    : ClauseBound.Inst.Half.lookT_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:13:53.386906+00:00
-- url     : https://prove2.me/theorems/6204b390-694e-40b5-aa11-a1f972351f10
-- title:
--   Half: look T poly T
-- statement:
--   Reading an entry of a table.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L55-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L55-L57

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

theorem ClauseBound.Inst.Half.lookT_polyT {flat : α → List (List ℕ)} {T : α → List ℤ} {π σ : α → List ℕ} (hf : PolyT flat) (hT : PolyT T)
    (hπ : PolyT π) (hσ : PolyT σ) : PolyT fun x => lookT (flat x) (T x) (π x) (σ x) := by sorry
