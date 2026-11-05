-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_beta0_le
-- name    : ClauseBound.ParityChecks.Params.Big.beta0_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:20.337638+00:00
-- url     : https://prove2.me/theorems/f8d63181-bcf2-4188-b30d-9c89f435ab1c
-- title:
--   Big: beta0 le
-- statement:
--   β₀ ≤ 3·⌈log₂(2Δ)⌉·(nb + 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L250-L265
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L250-L265

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

theorem ClauseBound.ParityChecks.Params.Big.beta0_le : beta0 m (nbOf n Δ) ≤ 3 * LD Δ * (nbOf n Δ + 1) := by sorry
