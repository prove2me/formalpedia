-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertPar_i0Of_unary
-- name    : ClauseBound.ParityChecks.CertPar.i0Of_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:20:44.608634+00:00
-- url     : https://prove2.me/theorems/e743cd08-baa0-4673-8c94-80fa2827f347
-- title:
--   Cert Par: i0 Of unary
-- statement:
--   i₀ is given in unary if n is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L48-L49
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertPar.lean#L48-L49

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

theorem ClauseBound.ParityChecks.CertPar.i0Of_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => i0Of (n x) := by sorry
