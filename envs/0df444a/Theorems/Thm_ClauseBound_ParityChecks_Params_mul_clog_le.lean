-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_mul_clog_le
-- name    : ClauseBound.ParityChecks.Params.mul_clog_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:00:43.993968+00:00
-- url     : https://prove2.me/theorems/f4555ff1-50d9-465f-955e-6058854fe5af
-- title:
--   Params: mul clog le
-- statement:
--   A·⌈log₂(ℓ + 1)⌉ ≤ ℓ for ℓ ≥ 2A².
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L119-L132
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L119-L132

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_ParityChecks_RunDefs
import Definitions.Def_ClauseBound_Rec_Few
import Definitions.Def_ClauseBound_ParityChecks_Params
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.ParityChecks
open Finset _root_.ParityChecks
open Params
open ClauseBound.ParityChecks.Params

theorem ClauseBound.ParityChecks.Params.mul_clog_le (A ℓ : ℕ) (hA : 1 ≤ A) (hℓ : 2 * A ^ 2 ≤ ℓ) : A * Nat.clog 2 (ℓ + 1) ≤ ℓ := by sorry
