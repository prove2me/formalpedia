-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_LD_unary
-- name    : ClauseBound.ParityChecks.CertPar.LD_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T23:43:11.192279+00:00
-- url     : https://prove2.me/theorems/9319e2ea-aace-4596-aa9f-bee440536e9c
-- title:
--   Cert Par: LD unary
-- statement:
--   ⌈log₂(2Δ)⌉ is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L34-L34
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L34-L34

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

theorem ClauseBound.ParityChecks.CertPar.LD_unary {Δ : α → ℕ} (hΔ : PolyT Δ) : Unary fun x => LD (Δ x) := by sorry
