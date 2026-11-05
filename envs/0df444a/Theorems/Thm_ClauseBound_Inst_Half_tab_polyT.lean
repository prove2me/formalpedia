-- Prove2me | Theorems.Thm_ClauseBound_Inst_Half_tab_polyT
-- name    : ClauseBound.Inst.Half.tab_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:16:12.020069+00:00
-- url     : https://prove2.me/theorems/69d1265f-ca33-42ec-88f5-d52414522bae
-- title:
--   Half: tab poly T
-- statement:
--   The table of a polynomial-time function of two listed monomials.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L47-L52
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Inst/CertHalfTab.lean#L47-L52

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

theorem ClauseBound.Inst.Half.tab_polyT {flat : α → List (List ℕ)} {f : α → List ℕ → List ℕ → ℤ} (hf : PolyT flat)
    (hg : PolyT fun p : α × List ℕ × List ℕ => f p.1 p.2.1 p.2.2) : PolyT fun x => tab (flat x) (f x) := by sorry
