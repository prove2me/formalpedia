-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_mod_two_pow_polyT
-- name    : ClauseBound.ParityChecks.CertLib.mod_two_pow_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T01:31:28.78372+00:00
-- url     : https://prove2.me/theorems/c91a933f-5ba9-4509-9ce4-b488f141ef1e
-- title:
--   Cert Lib: mod two pow poly T
-- statement:
--   The remainder of an integer modulo a power of 2 is polynomial-time, for the exponent in unary.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L97-L98
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L97-L98

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

theorem ClauseBound.ParityChecks.CertLib.mod_two_pow_polyT {a : α → ℤ} {k : α → ℕ} (ha : PolyT a) (hk : Unary k) : PolyT fun x => a x % 2 ^ k x := by sorry
