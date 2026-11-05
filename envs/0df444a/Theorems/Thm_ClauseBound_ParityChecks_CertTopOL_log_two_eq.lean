-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertTopOL_log_two_eq
-- name    : ClauseBound.ParityChecks.CertTopOL.log_two_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:25.611383+00:00
-- url     : https://prove2.me/theorems/a80c127d-c548-4e93-950f-0d82e2357b2a
-- title:
--   Cert Top OL: log two eq
-- statement:
--   ⌊log₂ n⌋ is the number of binary digits of n, less one.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L35-L40
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertTopOL.lean#L35-L40

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

theorem ClauseBound.ParityChecks.CertTopOL.log_two_eq (n : ℕ) : Nat.log 2 n = Nat.size n - 1 := by sorry
