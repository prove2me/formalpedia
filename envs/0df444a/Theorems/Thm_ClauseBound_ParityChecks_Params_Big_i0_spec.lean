-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_i0_spec
-- name    : ClauseBound.ParityChecks.Params.Big.i0_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:35:24.156035+00:00
-- url     : https://prove2.me/theorems/a4f15b17-52b7-4928-b6d2-77a13a21f413
-- title:
--   Big: i0 spec
-- statement:
--   20n ≤ ℓ·i₀ ≤ 20n + ℓ − 1.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L275-L282
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L275-L282

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

theorem ClauseBound.ParityChecks.Params.Big.i0_spec : 20 * n ≤ ℓ * i0Of n ∧ ℓ * i0Of n ≤ 20 * n + ℓ - 1 := by sorry
