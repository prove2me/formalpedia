-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_CertLib_log_polyT
-- name    : ClauseBound.ParityChecks.CertLib.log_polyT
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T00:41:27.610364+00:00
-- url     : https://prove2.me/theorems/13140956-d202-4b4b-a979-c77c8f10cd47
-- title:
--   Cert Lib: log poly T
-- statement:
--   ⌊log₂ n⌋ is polynomial-time.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L163-L164
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/CertLib.lean#L163-L164

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

theorem ClauseBound.ParityChecks.CertLib.log_polyT {n : α → ℕ} (hn : PolyT n) : PolyT fun x => Nat.log 2 (n x) := by sorry
