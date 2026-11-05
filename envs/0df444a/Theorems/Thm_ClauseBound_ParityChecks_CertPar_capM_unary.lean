-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_capM_unary
-- name    : ClauseBound.ParityChecks.CertPar.capM_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T04:53:53.115025+00:00
-- url     : https://prove2.me/theorems/be5fbd95-568a-4a07-9fde-598221ea1944
-- title:
--   Cert Par: cap M unary
-- statement:
--   The cap for the marks is given in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L86-L86
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L86-L86

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_ProgDefs
import Definitions.Def_ClauseBound_ParityChecks_CertLib
import Definitions.Def_PaddedDescent_F_CertMark
import Definitions.Def_ClauseBound_ParityChecks_CertPar
import Theorems.Thm_PaddedDescent_F_CertGrid_capM_unary

set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertPar
open Groundwork PaddedDescent.F ClauseBound.ParityChecks.CertLib
variable {α : Type} [Enc α]
variable {q : α → Par} (hq : QU q)
include hq

theorem ClauseBound.ParityChecks.CertPar.capM_unary : Unary fun x => capM (q x) := by sorry
