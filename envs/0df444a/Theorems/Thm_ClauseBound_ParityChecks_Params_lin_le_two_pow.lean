-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_lin_le_two_pow
-- name    : ClauseBound.ParityChecks.Params.lin_le_two_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:20.453863+00:00
-- url     : https://prove2.me/theorems/91359538-3bce-4405-a43f-94df2deae07f
-- title:
--   Params: lin le two pow
-- statement:
--   200·ℓ + 300 ≤ 2^ℓ for ℓ ≥ 12.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L135-L138
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L135-L138

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

theorem ClauseBound.ParityChecks.Params.lin_le_two_pow (ℓ : ℕ) (h : 12 ≤ ℓ) : 200 * ℓ + 300 ≤ 2 ^ ℓ := by sorry
