-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_colMax_unary
-- name    : ClauseBound.ParityChecks.CertPar.colMax_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:19:03.641705+00:00
-- url     : https://prove2.me/theorems/b9587124-574f-4e62-895a-32e5fcc06b2a
-- title:
--   Cert Par: col Max unary
-- statement:
--   The bound for the number of checks that contain a clause is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L91-L92
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L91-L92

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

theorem ClauseBound.ParityChecks.CertPar.colMax_unary {n Δ : α → ℕ} (hn : PolyT n) (hΔ : PolyT Δ) : Unary fun x => colMax (n x) (Δ x) := by sorry
