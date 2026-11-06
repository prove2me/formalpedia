-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_occOL_unary
-- name    : ClauseBound.ParityChecks.CertTopOL.occOL_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:22:29.12277+00:00
-- url     : https://prove2.me/theorems/0fc43191-d0c8-4934-a626-e6d97bc451de
-- title:
--   Cert Top OL: occ OL unary
-- statement:
--   The Cert Top OL construction uses the occ OL unary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L90-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L90-L92

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_TopDefs
import Definitions.Def_ClauseBound_TopN_Cert
import Definitions.Def_ClauseBound_Inst_RecArith
import Definitions.Def_ClauseBound_ParityChecks_CertTopOL
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertTopOL
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open ClauseBound.TopN ClauseBound.TopN.Cert ClauseBound.ParityChecks
variable {α : Type} [Enc α]
variable {K n s D : α → ℕ}

theorem ClauseBound.ParityChecks.CertTopOL.occOL_unary (hn : Unary n) (hD : Unary D) : Unary fun x => occOL (n x) (D x) := by sorry
