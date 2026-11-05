-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_UbOL_unary
-- name    : ClauseBound.ParityChecks.CertPar.UbOL_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:21:18.03871+00:00
-- url     : https://prove2.me/theorems/193d1f52-ad11-4034-8a34-2539a53dfbb8
-- title:
--   Cert Par: Ub OL unary
-- statement:
--   The bound for the shared bits of the networks is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L127-L128
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L127-L128

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

theorem ClauseBound.ParityChecks.CertPar.UbOL_unary (k : ℕ) {K n Δ : α → ℕ} (hK : Unary K) (hn : Unary n) (hΔ : Unary Δ) : Unary fun x => UbOL k (K x) (n x) (Δ x) := by sorry
