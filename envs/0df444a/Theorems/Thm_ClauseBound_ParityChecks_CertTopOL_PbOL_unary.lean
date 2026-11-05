-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_PbOL_unary
-- name    : ClauseBound.ParityChecks.CertTopOL.PbOL_unary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:22:40.566006+00:00
-- url     : https://prove2.me/theorems/9756d631-4d0c-4ad6-ad32-1b2dd79e89dc
-- title:
--   Cert Top OL: Pb OL unary
-- statement:
--   The bound on the size is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L100-L104
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L100-L104

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

theorem ClauseBound.ParityChecks.CertTopOL.PbOL_unary (hK : Unary K) (hn : Unary n) (hD : Unary D) : Unary fun x => PbOL (K x) (n x) (D x) := by sorry
