-- Prove2me | Theorems.Thm_ClauseBound_Alg_CertLevel_needCut_eq
-- name    : ClauseBound.Alg.CertLevel.needCut_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:05:07.565226+00:00
-- url     : https://prove2.me/theorems/abb14afe-eb22-4df4-b3fa-dfde0a72f2b4
-- title:
--   Cert Level: need Cut eq
-- statement:
--   With M the sum of all numbers of nodes, the cut-off changes nothing.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L470-L486
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Alg/CertLevel.lean#L470-L486

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Alg_Interfaces
import Definitions.Def_PaddedDescent_F_FuelCert
import Definitions.Def_ToTuring_Poly_Digits
import Definitions.Def_ClauseBound_Alg_CertLevel
import Theorems.Thm_Groundwork_PolyT_map
import Theorems.Thm_Groundwork_PolyT_sum
attribute [local fun_prop] Groundwork.PolyT.map
attribute [local fun_prop] Groundwork.PolyT.sum


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Alg ClauseBound.Alg.CertLevel
open Groundwork Groundwork.Prog Groundwork.Grid PaddedDescent.F
variable {α : Type} [Enc α] {P : PiecesF}

theorem ClauseBound.Alg.CertLevel.needCut_eq (P : PiecesF) (b : U) (Kup lam B : ℕ) (sched : List Step) :
    needCut P (Kup + (sched.map Step.K).sum) b Kup lam B sched = needC P b Kup lam B sched := by sorry
