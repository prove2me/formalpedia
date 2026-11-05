-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_beta0_unary
-- name    : ClauseBound.ParityChecks.CertPar.beta0_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:18:42.211402+00:00
-- url     : https://prove2.me/theorems/5fcf18c5-03df-4314-a5ea-62f580845fa8
-- title:
--   Cert Par: beta0 unary
-- statement:
--   β₀ is given in unary if nb is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L40-L41
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L40-L41

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

theorem ClauseBound.ParityChecks.CertPar.beta0_unary {m nb : α → ℕ} (hm : PolyT m) (hnb : Unary nb) : Unary fun x => beta0 (m x) (nb x) := by sorry
