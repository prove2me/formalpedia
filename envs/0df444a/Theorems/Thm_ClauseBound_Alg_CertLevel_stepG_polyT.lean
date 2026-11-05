-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_stepG_polyT
-- name    : ClauseBound.Alg.CertLevel.stepG_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:02:55.593828+00:00
-- url     : https://prove2.me/theorems/21536dcc-2008-4c00-92fa-c894f8f42f24
-- title:
--   Cert Level: step G poly T
-- statement:
--   One round of the descent.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L234-L246
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L234-L246

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

theorem ClauseBound.Alg.CertLevel.stepG_polyT (hP : P.Keeps) (hL : StCertLam P) (hX : StCertExpandG P) {pad : α → U} {st : α → DState} {s : α → Step} (hp : PolyT pad)
    (hst : PolyT st) (hs : PolyT s) : PolyT fun x => stepG P (pad x) (st x) (s x) := by sorry
