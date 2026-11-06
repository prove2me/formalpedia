-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_gridW_polyT
-- name    : ClauseBound.Alg.CertGridG.gridW_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:59:19.935891+00:00
-- url     : https://prove2.me/theorems/ae02695e-41cf-49cb-932e-b865147b8d74
-- title:
--   Cert Grid G: grid W poly T
-- statement:
--   The weight of a part is polynomial-time, for p and d in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L158-L162
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L158-L162

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

theorem ClauseBound.Alg.CertGridG.gridW_polyT {p d ℓ : α → ℕ} {tr : α → Bool} {T : α → Tab} {q : α → WQ} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) (hℓ : PolyT ℓ)
    (hT : PolyT T) (hq : PolyT q) : PolyT fun x => gridW (p x) (d x) (tr x) (ℓ x) (T x) (q x) := by sorry
