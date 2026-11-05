-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_expandG_polyT
-- name    : ClauseBound.Alg.CertLevel.expandG_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:02:33.851809+00:00
-- url     : https://prove2.me/theorems/e9edf108-9038-446e-9f64-4edfdc7b70d7
-- title:
--   Cert Level: expand G poly T
-- statement:
--   One level.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L206-L223
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L206-L223

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
variable (hP : P.Keeps)
include hP

theorem ClauseBound.Alg.CertLevel.expandG_polyT (hG : StCertGrid P) (hL : StCertLam P) (hE : StCertEnum) (hR : StCertRebalG) {pad : α → U} {s : α → Step} {I : α → PInst}
    (hp : PolyT pad) (hs : PolyT s) (hI : PolyT I) : PolyT fun x => expandG P (pad x) (s x) (I x) := by sorry
