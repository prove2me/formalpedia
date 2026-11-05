-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_ediv_natCast
-- name    : ClauseBound.ParityChecks.CertLib.ediv_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:18:18.25723+00:00
-- url     : https://prove2.me/theorems/b558a73b-cf65-46a9-8539-071e83c4fcc8
-- title:
--   Cert Lib: ediv nat Cast
-- statement:
--   The quotient of an integer by a natural number, rounded down, by cases on the sign.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L68-L83
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L68-L83

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

theorem ClauseBound.ParityChecks.CertLib.ediv_natCast (a : ℤ) (b : ℕ) :
    a / (b : ℤ) = if 0 ≤ a then ((a.toNat / b : ℕ) : ℤ) else if b = 0 then 0 else -(((a.natAbs - 1) / b + 1 : ℕ) : ℤ) := by sorry
