-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_needStep_polyT
-- name    : ClauseBound.Alg.CertLevel.needStep_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:04:24.862637+00:00
-- url     : https://prove2.me/theorems/0591792b-5048-4b9f-aaed-1b687317bfd1
-- title:
--   Cert Level: need Step poly T
-- statement:
--   One step of the computation of the exponent, if the number of nodes in the state is given in
--   unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L388-L413
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L388-L413

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.needStep_polyT (hP : P.Keeps) (hL : StCertLam P) {st : α → NState} {s : α → Step} (hst : PolyT st) (hs : PolyT s)
    (hK : Unary fun x => (st x).2.2.1) : PolyT fun x => needStep P (st x) (s x) := by sorry
