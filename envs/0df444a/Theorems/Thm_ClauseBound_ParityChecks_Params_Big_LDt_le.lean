-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_LDt_le
-- name    : ClauseBound.ParityChecks.Params.Big.LDt_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:32:03.565308+00:00
-- url     : https://prove2.me/theorems/52f4295f-c8db-4ebf-9012-4f8b796947f1
-- title:
--   Big: LDt le
-- statement:
--   42·(⌈log₂(2Δ)⌉ + t) ≤ ℓ.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L230-L231
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L230-L231

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
open ClauseBound.ParityChecks.Params.Big
variable {c n Δ m ℓ t : ℕ} (b : Big c n Δ m ℓ t)
include b

theorem ClauseBound.ParityChecks.Params.Big.LDt_le : 42 * (LD Δ + t) ≤ ℓ := by sorry
