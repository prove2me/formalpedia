-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_nMemb_unary
-- name    : ClauseBound.Alg.CertGridG.nMemb_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:13:36.647694+00:00
-- url     : https://prove2.me/theorems/4692a79a-dd51-43e3-a384-28ae355a2289
-- title:
--   Cert Grid G: n Memb unary
-- statement:
--   The number of nodes of a part is given in unary if p and d are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L121-L123
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L121-L123

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

theorem ClauseBound.Alg.CertGridG.nMemb_unary {p d : α → ℕ} {tr : α → Bool} (hp : Unary p) (hd : Unary d) (ht : PolyT tr) :
    Unary fun x => nMemb (p x) (d x) (tr x) := by sorry
