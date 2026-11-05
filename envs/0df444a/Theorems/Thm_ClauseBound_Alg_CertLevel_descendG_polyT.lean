-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_descendG_polyT
-- name    : ClauseBound.Alg.CertLevel.descendG_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:03:07.245205+00:00
-- url     : https://prove2.me/theorems/c6b494be-987c-47cd-9086-53c4b0c75de2
-- title:
--   Cert Level: descend G poly T
-- statement:
--   The descent through all levels.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L249-L252
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L249-L252

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

theorem ClauseBound.Alg.CertLevel.descendG_polyT (hP : P.Keeps) (hL : StCertLam P) (hX : StCertExpandG P) {pad : α → U} {sched : α → List Step} {I : α → PInst}
    (hp : PolyT pad) (hs : PolyT sched) (hI : PolyT I) : PolyT fun x => descendG P (pad x) (sched x) (I x) := by sorry
