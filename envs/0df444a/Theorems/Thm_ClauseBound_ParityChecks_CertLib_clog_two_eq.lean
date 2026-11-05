-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_clog_two_eq
-- name    : ClauseBound.ParityChecks.CertLib.clog_two_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:41:02.96521+00:00
-- url     : https://prove2.me/theorems/0560f45d-05ae-42da-920e-fd5f841259db
-- title:
--   Cert Lib: clog two eq
-- statement:
--   ⌈log₂ n⌉ is the number of binary digits of n − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L141-L152
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L141-L152

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

theorem ClauseBound.ParityChecks.CertLib.clog_two_eq (n : ℕ) : Nat.clog 2 n = Nat.size (n - 1) := by sorry
