-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_key
-- name    : ClauseBound.ParityChecks.Params.Big.key
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:26:26.702958+00:00
-- url     : https://prove2.me/theorems/d5d3ca05-d400-4b16-b0a9-0308f960bb85
-- title:
--   Big: key
-- statement:
--   6·m·2^{⌈ℓ/2⌉} ≤ nb·i₀.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L433-L447
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L433-L447

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

theorem ClauseBound.ParityChecks.Params.Big.key : 6 * m * 2 ^ (ℓ - ℓ / 2) ≤ nbOf n Δ * i0Of n := by sorry
