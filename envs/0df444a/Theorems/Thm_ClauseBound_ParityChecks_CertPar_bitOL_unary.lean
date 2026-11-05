-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_bitOL_unary
-- name    : ClauseBound.ParityChecks.CertPar.bitOL_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:42:26.644359+00:00
-- url     : https://prove2.me/theorems/d561958f-920f-475e-aac9-61eaa9e19952
-- title:
--   Cert Par: bit OL unary
-- statement:
--   The number of bits of a position in a block is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L107-L107
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L107-L107

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

theorem ClauseBound.ParityChecks.CertPar.bitOL_unary {Δ : α → ℕ} (hΔ : Unary Δ) : Unary fun x => bitOL (Δ x) := by sorry
