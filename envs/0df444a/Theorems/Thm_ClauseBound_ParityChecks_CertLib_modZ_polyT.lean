-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_modZ_polyT
-- name    : ClauseBound.ParityChecks.CertLib.modZ_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T03:19:47.416199+00:00
-- url     : https://prove2.me/theorems/bb6f48c6-cfd0-4fb6-bf4c-c6acc8542dc4
-- title:
--   Cert Lib: mod Z poly T
-- statement:
--   The remainder of an integer modulo a natural number is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L60-L65
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L60-L65

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

theorem ClauseBound.ParityChecks.CertLib.modZ_polyT {a : α → ℤ} {b : α → ℕ} (ha : PolyT a) (hb : PolyT b) : PolyT fun x => a x % (b x : ℤ) := by sorry
