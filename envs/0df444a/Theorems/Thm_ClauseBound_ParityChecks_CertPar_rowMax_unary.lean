-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_rowMax_unary
-- name    : ClauseBound.ParityChecks.CertPar.rowMax_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:04.037293+00:00
-- url     : https://prove2.me/theorems/d87a7834-e70d-4f23-bbb3-9cc8460ea43b
-- title:
--   Cert Par: row Max unary
-- statement:
--   The bound for the number of clauses of a check is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L95-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L95-L96

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

theorem ClauseBound.ParityChecks.CertPar.rowMax_unary {n Δ : α → ℕ} (hn : PolyT n) (hΔ : Unary Δ) : Unary fun x => rowMax (n x) (Δ x) := by sorry
