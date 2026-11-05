-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_countP_le_range
-- name    : ClauseBound.Alg.CertLevel.countP_le_range
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:02:49.713677+00:00
-- url     : https://prove2.me/theorems/ca4da90d-ca6b-4cac-8c4b-432c88bf9e10
-- title:
--   Cert Level: count P le range
-- statement:
--   Among 0, …, N − 1 there are min N (k + 1) numbers that are at most k.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L269-L276
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L269-L276

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_Groundwork_PolyT_countP
attribute [local fun_prop] Groundwork.PolyT.countP


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.countP_le_range (k N : ℕ) : (List.range N).countP (fun r => decide (r ≤ k)) = min N (k + 1) := by sorry
