-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertOL_CU_comp
-- name    : ClauseBound.ParityChecks.CertOL.CU.comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:32:13.762148+00:00
-- url     : https://prove2.me/theorems/5fd35116-1581-4c54-98df-c51a5c887681
-- title:
--   CU: comp
-- statement:
--   The property passes to a polynomial-time change of the context.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L98-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertOL.lean#L98-L100

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Definitions.Def_ClauseBound_ParityChecks_CertNum
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_ParityChecks_CertOL
import Theorems.Thm_ClauseBound_ParityChecks_CertLib_QU_comp
import Theorems.Thm_Groundwork_PB_comp
import Theorems.Thm_Groundwork_PolyT_comp
import Theorems.Thm_Groundwork_Unary_comp
attribute [local fun_prop] Groundwork.PolyT.comp


set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertOL
open Groundwork Groundwork.Prog PaddedDescent.F PaddedDescent.F.Mark ClauseBound.Alg ClauseBound.TopN ClauseBound.TopN.EvalW ClauseBound.ParityChecks.CertLib ClauseBound.ParityChecks.CertPar
variable {α : Type} [Enc α]
variable {Idx : Type} [Enc Idx] {S : Solver Idx}

theorem ClauseBound.ParityChecks.CertOL.CU.comp {β : Type} [Enc β] {pad : α → U} {i : α → Idx} {n Δ : α → ℕ} {q : α → Par} (h : CU pad i n Δ q) {g : β → α} (hg : PolyT g) :
    CU (fun y => pad (g y)) (fun y => i (g y)) (fun y => n (g y)) (fun y => Δ (g y)) (fun y => q (g y)) := by sorry
