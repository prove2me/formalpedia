-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_nPat_polyT
-- name    : ClauseBound.Alg.CertLevel.nPat_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:17:23.142687+00:00
-- url     : https://prove2.me/theorems/2cd89cd8-722e-4db7-bcfa-db96017a4f72
-- title:
--   Cert Level: n Pat poly T
-- statement:
--   The number of patterns.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L109-L110
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L109-L110

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_Groundwork_PolyT_length
attribute [local fun_prop] Groundwork.PolyT.length


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}
variable (hP : P.Keeps)
include hP

theorem ClauseBound.Alg.CertLevel.nPat_polyT {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => nPat P (s x) (l x).length := by sorry
