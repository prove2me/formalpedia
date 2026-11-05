-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_Ub_unary
-- name    : ClauseBound.ParityChecks.CertPar.Ub_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:43.948203+00:00
-- url     : https://prove2.me/theorems/d10e534c-23ce-4657-aa6b-8631e38d1da9
-- title:
--   Cert Par: Ub unary
-- statement:
--   The bound for the shared bits of a network of marks is given in unary if its arguments are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L114-L117
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L114-L117

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

theorem ClauseBound.ParityChecks.CertPar.Ub_unary (k : ℕ) {g n w β R : α → ℕ} (hg : Unary g) (hn : Unary n) (hw : Unary w) (hβ : Unary β) (hR : Unary R) :
    Unary fun x => Ub k (g x) (n x) (w x) (β x) (R x) := by sorry
