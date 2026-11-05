-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_start_parOf
-- name    : ClauseBound.ParityChecks.start_parOf
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:17.022415+00:00
-- url     : https://prove2.me/theorems/2cb24360-71ff-4e0a-880f-ba7126592e61
-- title:
--   Parity Checks: start par Of
-- statement:
--   The conditions that need no largeness of n.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L81-L96
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L81-L96

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

theorem ClauseBound.ParityChecks.start_parOf (n Δ m : ℕ) : (5 / 8 : ℚ) ^ (parOf n Δ m).r * (2 ^ n * m.choose ((parOf n Δ m).nb + 1) : ℕ) ≤ 1 / 8 := by sorry
