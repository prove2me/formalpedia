-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_needFin_polyT
-- name    : ClauseBound.Alg.CertLevel.needFin_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:04:37.679076+00:00
-- url     : https://prove2.me/theorems/b6cde1d2-f906-4ddc-8b90-76d893744b9e
-- title:
--   Cert Level: need Fin poly T
-- statement:
--   The end of that computation, if the number of nodes in the state is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L416-L421
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L416-L421

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

theorem ClauseBound.Alg.CertLevel.needFin_polyT {st : α → NState} (hst : PolyT st) (hK : Unary fun x => (st x).2.2.1) : PolyT fun x => needFin (st x) := by sorry
