-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_nbOf_unary
-- name    : ClauseBound.ParityChecks.CertPar.nbOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:19:47.419397+00:00
-- url     : https://prove2.me/theorems/012233c4-3b78-40c3-b8a1-70b19f92b05b
-- title:
--   Cert Par: nb Of unary
-- statement:
--   nb is given in unary if n is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L37-L37
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L37-L37

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

theorem ClauseBound.ParityChecks.CertPar.nbOf_unary {n Δ : α → ℕ} (hn : Unary n) (hΔ : PolyT Δ) : Unary fun x => nbOf (n x) (Δ x) := by sorry
