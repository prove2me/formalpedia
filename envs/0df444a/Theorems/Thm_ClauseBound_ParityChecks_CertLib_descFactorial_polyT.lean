-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_descFactorial_polyT
-- name    : ClauseBound.ParityChecks.CertLib.descFactorial_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:19:47.114551+00:00
-- url     : https://prove2.me/theorems/07de6604-0c59-4453-9357-dd140f2097d9
-- title:
--   Cert Lib: desc Factorial poly T
-- statement:
--   n(n − 1)⋯(n − k + 1) is polynomial-time, for k in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L130-L134
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L130-L134

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

theorem ClauseBound.ParityChecks.CertLib.descFactorial_polyT {n k : α → ℕ} (hn : PolyT n) (hk : Unary k) : PolyT fun x => (n x).descFactorial (k x) := by sorry
