-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_needCut_polyT
-- name    : ClauseBound.Alg.CertLevel.needCut_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:05:08.423552+00:00
-- url     : https://prove2.me/theorems/f141a39b-b0bc-4fa7-a231-2c87e181cbb5
-- title:
--   Cert Level: need Cut poly T
-- statement:
--   The computation with the cut-off is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L497-L514
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L497-L514

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

theorem ClauseBound.Alg.CertLevel.needCut_polyT (hP : P.Keeps) (hL : StCertLam P) {M Kup lam B : α → ℕ} {b : α → U} {sched : α → List Step} (hM : Unary M) (hb : PolyT b)
    (hK : PolyT Kup) (hl : Unary lam) (hB : PolyT B) (hs : PolyT sched) :
    PolyT fun x => needCut P (M x) (b x) (Kup x) (lam x) (B x) (sched x) := by sorry
