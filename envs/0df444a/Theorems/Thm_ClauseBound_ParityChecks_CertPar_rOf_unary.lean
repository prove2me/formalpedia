-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_rOf_unary
-- name    : ClauseBound.ParityChecks.CertPar.rOf_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:38.809947+00:00
-- url     : https://prove2.me/theorems/0c49fed6-85d6-49f2-9ade-57209b0c2be4
-- title:
--   Cert Par: r Of unary
-- statement:
--   r is given in unary if n and β₀ are.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L44-L45
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L44-L45

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

theorem ClauseBound.ParityChecks.CertPar.rOf_unary {n b : α → ℕ} (hn : Unary n) (hb : Unary b) : Unary fun x => rOf (n x) (b x) := by sorry
