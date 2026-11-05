-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_instLen_polyT
-- name    : ClauseBound.Alg.CertLevel.instLen_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:17:58.889635+00:00
-- url     : https://prove2.me/theorems/2d063d85-a291-4526-95d2-b811aea49407
-- title:
--   Cert Level: inst Len poly T
-- statement:
--   The length of the word of an instance, for K and the label length in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L312-L319
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L312-L319

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

theorem ClauseBound.Alg.CertLevel.instLen_polyT {K lam B : α → ℕ} (hK : Unary K) (hl : Unary lam) (hB : PolyT B) : PolyT fun x => instLen (K x) (lam x) (B x) := by sorry
