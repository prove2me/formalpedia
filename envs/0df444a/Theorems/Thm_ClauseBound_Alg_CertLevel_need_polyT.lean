-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_need_polyT
-- name    : ClauseBound.Alg.CertLevel.need_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:03:26.913845+00:00
-- url     : https://prove2.me/theorems/4683c9b5-575e-4f6e-b3cd-c8f6d154a0d1
-- title:
--   Cert Level: need poly T
-- statement:
--   The exponent that the loops inside the pieces need.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L339-L340
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L339-L340

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

theorem ClauseBound.Alg.CertLevel.need_polyT (hP : P.Keeps) {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) : PolyT fun x => P.need (s x).h (l x).length := by sorry
