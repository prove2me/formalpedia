-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_g_unary
-- name    : ClauseBound.ParityChecks.CertPar.g_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:50:56.490316+00:00
-- url     : https://prove2.me/theorems/59ec56e8-1a99-480c-bdf6-59e4dd6d06e7
-- title:
--   Cert Par: g unary
-- statement:
--   3K⁸ is given in unary if K is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L124-L124
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L124-L124

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertPar.g_unary {K : α → ℕ} (hK : Unary K) : Unary fun x => 3 * K x ^ 8 := by sorry
