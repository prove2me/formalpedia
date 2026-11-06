-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_beta1_unary
-- name    : ClauseBound.ParityChecks.CertPar.beta1_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:43.241855+00:00
-- url     : https://prove2.me/theorems/565da08d-8f9a-4731-82dd-64919c6b5edd
-- title:
--   Cert Par: beta1 unary
-- statement:
--   β₁ is given in unary if i₀ is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L52-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L52-L54

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

theorem ClauseBound.ParityChecks.CertPar.beta1_unary {m i : α → ℕ} (hm : PolyT m) (hi : Unary i) : Unary fun x => beta1 (m x) (i x) := by sorry
