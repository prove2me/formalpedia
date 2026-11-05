-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_parM_polyT
-- name    : ClauseBound.ParityChecks.CertPar.parM_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:19.614804+00:00
-- url     : https://prove2.me/theorems/425d4ef9-d268-45bf-a0be-82fa97c0405f
-- title:
--   Cert Par: par M poly T
-- statement:
--   The parameters of the network of marks are polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L110-L111
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L110-L111

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

theorem ClauseBound.ParityChecks.CertPar.parM_polyT {q : α → Par} (hq : QU q) {n Δ : α → ℕ} (hn : Unary n) (hΔ : Unary Δ) : PolyT fun x => parM (n x) (Δ x) (q x) := by sorry
