-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_restO_aux
-- name    : ClauseBound.ParityChecks.CertTopOL.restO_aux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:41.123695+00:00
-- url     : https://prove2.me/theorems/3492a5e2-a5d7-4f83-9032-2f5ee9db9f6b
-- title:
--   Cert Top OL: rest O aux
-- statement:
--   The formula of the exponent for everything but the networks, for any polynomial-time numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L107-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L107-L111

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

theorem ClauseBound.ParityChecks.CertTopOL.restO_aux (k : ℕ) {Z₁ Z₂ B z q : α → ℕ} (hK : PolyT K) (h1 : PolyT Z₁) (h2 : PolyT Z₂) (hB : PolyT B) (hz : PolyT z) (hn : PolyT n) (hq : PolyT q) :
    PolyT fun x => 3 * K x ^ 8 * (3 * K x ^ 8) * 3 * Z₁ x + (3 * Z₂ x + 3 * z x + 12) + (n x / q x + 2) + (B x + 5 * k + 10 + (k + 3) * z x) := by sorry
