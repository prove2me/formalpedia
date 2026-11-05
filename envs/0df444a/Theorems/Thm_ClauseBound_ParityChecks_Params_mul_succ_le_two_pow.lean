-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_mul_succ_le_two_pow
-- name    : ClauseBound.ParityChecks.Params.mul_succ_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:16.302358+00:00
-- url     : https://prove2.me/theorems/e72b0e07-0673-496d-b5f6-105e4bbb3529
-- title:
--   Params: mul succ le two pow
-- statement:
--   x·(x + 1) ≤ 2^{x+1}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L109-L116
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L109-L116

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

theorem ClauseBound.ParityChecks.Params.mul_succ_le_two_pow (x : ℕ) : x * (x + 1) ≤ 2 ^ (x + 1) := by sorry
