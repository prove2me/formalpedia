-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_dpow_polyT
-- name    : ClauseBound.Alg.CertLevel.dpow_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:01:24.618548+00:00
-- url     : https://prove2.me/theorems/0de223e3-797a-4a41-bc30-736078d9d408
-- title:
--   Cert Level: dpow poly T
-- statement:
--   The factor d^R of a step.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L104-L106
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L104-L106

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

theorem ClauseBound.Alg.CertLevel.dpow_polyT {s : α → Step} {l : α → U} (hs : PolyT s) (hl : PolyT l) :
    PolyT fun x => P.d (s x).h (l x).length ^ nRectG (s x).p (s x).d := by sorry
