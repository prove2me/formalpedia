-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_chkG_polyT
-- name    : ClauseBound.Alg.CertGridG.chkG_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:14:46.759665+00:00
-- url     : https://prove2.me/theorems/961f4250-618c-4074-9d30-811661fa46e9
-- title:
--   Cert Grid G: chk G poly T
-- statement:
--   The test of the edges inside a part is polynomial-time, for p and d in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L151-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L151-L155

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_PaddedDescent_F_CertGrid
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ToTuring_Poly_Words
import Definitions.Def_ClauseBound_Alg_CertGridG
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertGridG
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α]

theorem ClauseBound.Alg.CertGridG.chkG_polyT {p d ℓ : α → ℕ} {tr : α → Bool} {q : α → WQ} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hℓ : PolyT ℓ)
    (hq : PolyT q) : PolyT fun x => chkG (p x) (d x) (tr x) (ℓ x) (q x) := by sorry
