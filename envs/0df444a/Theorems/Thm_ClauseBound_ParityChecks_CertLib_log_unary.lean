-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_log_unary
-- name    : ClauseBound.ParityChecks.CertLib.log_unary
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:31:44.444586+00:00
-- url     : https://prove2.me/theorems/0545f05f-0d2e-4cbc-9b14-972a26403523
-- title:
--   Cert Lib: log unary
-- statement:
--   ⌊log₂ n⌋ is given in unary if n is.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L167-L168
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L167-L168

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Alg_CertGridG
import Definitions.Def_ClauseBound_ParityChecks_CertLib
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks ClauseBound.ParityChecks.CertLib
open Groundwork PaddedDescent.F
variable {α : Type} [Enc α]

theorem ClauseBound.ParityChecks.CertLib.log_unary {n : α → ℕ} (hn : Unary n) : Unary fun x => Nat.log 2 (n x) := by sorry
