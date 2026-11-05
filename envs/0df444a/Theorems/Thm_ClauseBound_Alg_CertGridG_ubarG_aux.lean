-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_ubarG_aux
-- name    : ClauseBound.Alg.CertGridG.ubarG_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T02:59:44.240448+00:00
-- url     : https://prove2.me/theorems/c4a3bfe8-b64f-4ba6-bc07-ece5585dafb8
-- title:
--   Cert Grid G: ubar G aux
-- statement:
--   The formula of the bound for U, for any numbers given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L272-L276
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L272-L276

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

theorem ClauseBound.Alg.CertGridG.ubarG_aux {thin : α → Bool} {N a p d lam R cs : α → ℕ} (h0 : PolyT thin) (h1 : Unary N) (h2 : PolyT a) (h3 : Unary p) (h4 : Unary d)
    (h5 : Unary lam) (h6 : Unary R) (h7 : Unary cs) :
    Unary fun x => if thin x = true then N x - N x / a x + (p x * d x) ^ 2 else p x * (p x - 1) * d x * lam x + R x * cs x := by sorry
