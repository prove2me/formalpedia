-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertGridG_D_unary__6c8f65
-- name    : ClauseBound.Alg.CertGridG.D_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T22:15:58.129743+00:00
-- url     : https://prove2.me/theorems/6c8f65b2-99b3-4f85-b730-ae3bbf12a7bc
-- title:
--   Cert Grid G: D unary
-- statement:
--   D is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L253-L253
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertGridG.lean#L253-L253

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
variable {s : α → Step} (hs : PolyT s)
include hs

theorem ClauseBound.Alg.CertGridG.D_unary : Unary fun x => (s x).D := by sorry
