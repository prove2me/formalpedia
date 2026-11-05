-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_emod_natCast
-- name    : ClauseBound.ParityChecks.CertLib.emod_natCast
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:19:39.078439+00:00
-- url     : https://prove2.me/theorems/b4773b6f-7181-4051-bc29-215689fecc28
-- title:
--   Cert Lib: emod nat Cast
-- statement:
--   The remainder of an integer modulo a natural number, by cases on the sign.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L41-L57
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L41-L57

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

theorem ClauseBound.ParityChecks.CertLib.emod_natCast (a : ℤ) (b : ℕ) :
    a % (b : ℤ) = if 0 ≤ a then ((a.toNat % b : ℕ) : ℤ) else if b = 0 then a else ((b - 1 - (a.natAbs - 1) % b : ℕ) : ℤ) := by sorry
