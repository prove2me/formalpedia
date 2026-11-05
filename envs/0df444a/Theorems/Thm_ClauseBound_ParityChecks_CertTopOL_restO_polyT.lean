-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_restO_polyT
-- name    : ClauseBound.ParityChecks.CertTopOL.restO_polyT
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T03:19:25.502195+00:00
-- url     : https://prove2.me/theorems/71282383-1055-4fa7-971a-8ae46422c474
-- title:
--   Cert Top OL: rest O poly T
-- statement:
--   The exponent for everything but the networks is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L114-L119
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L114-L119

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

theorem ClauseBound.ParityChecks.CertTopOL.restO_polyT (k : ℕ) (hK : Unary K) (hn : Unary n) (hs : Unary s) : PolyT fun x => restO k (K x) (n x) (s x) := by sorry
