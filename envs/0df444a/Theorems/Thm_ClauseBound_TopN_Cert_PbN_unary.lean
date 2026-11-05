-- Prove2me | Theorems.Thm_ClauseBound_TopN_Cert_PbN_unary
-- name    : ClauseBound.TopN.Cert.PbN_unary
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T22:58:14.493205+00:00
-- url     : https://prove2.me/theorems/5a462506-cb24-491f-80f2-bc8051eba7ef
-- title:
--   Cert: Pb N unary
-- statement:
--   The bound on the size is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Cert.lean#L76-L80
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/TopN/Cert.lean#L76-L80

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_TopN_Defs
import Definitions.Def_ClauseBound_Alg_CertTop
import Definitions.Def_CountKSatRate_Cert
import Definitions.Def_PaddedDescent_F_CertEval
import Definitions.Def_ClauseBound_TopN_Cert
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.TopN ClauseBound.TopN.Cert
open Groundwork Groundwork.Prog Groundwork.Sparsify CountKSat CountKSat.Poly PaddedDescent PaddedDescent.F PaddedDescent.F.CertTop PaddedDescent.F.CertEval CountKSatRate CountKSatRate.Cert ClauseBound.Alg ClauseBound.Alg.CertTop
open PaddedDescent.F.Mark (MCtx Cl cls nProf adm markF placeE)
variable {α : Type} [Enc α]
variable {K n s : α → ℕ}

theorem ClauseBound.TopN.Cert.PbN_unary (k : ℕ) (hK : Unary K) (hn : Unary n) (hs : Unary s) : Unary fun x => PbN k (K x) (n x) (s x) := by sorry
