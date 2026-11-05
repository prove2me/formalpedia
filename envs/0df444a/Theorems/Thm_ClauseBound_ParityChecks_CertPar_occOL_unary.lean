-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_occOL_unary
-- name    : ClauseBound.ParityChecks.CertPar.occOL_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:59.464201+00:00
-- url     : https://prove2.me/theorems/09ecc179-eda8-45f6-9933-fd8a6cf8d88c
-- title:
--   Cert Par: occ OL unary
-- statement:
--   The bound for the number of clauses in which a variable occurs is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L99-L100
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L99-L100

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

theorem ClauseBound.ParityChecks.CertPar.occOL_unary {n Δ : α → ℕ} (hn : PolyT n) (hΔ : Unary Δ) : Unary fun x => occOL (n x) (Δ x) := by sorry
