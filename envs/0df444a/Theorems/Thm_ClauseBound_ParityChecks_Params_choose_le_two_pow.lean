-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_choose_le_two_pow
-- name    : ClauseBound.ParityChecks.Params.choose_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:35:33.955919+00:00
-- url     : https://prove2.me/theorems/06b0eafd-20ff-435f-9bc0-676ce1ded0ac
-- title:
--   Params: choose le two pow
-- statement:
--   C(N, j) ≤ 2^{w·k} for j ≤ k ≤ N, if 3N ≤ k·2^w.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L141-L156
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L141-L156

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

theorem ClauseBound.ParityChecks.Params.choose_le_two_pow {N k j w : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ N) (hj : j ≤ k) (hw : 3 * N ≤ k * 2 ^ w) : N.choose j ≤ 2 ^ (w * k) := by sorry
