-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_poly_le
-- name    : ClauseBound.ParityChecks.Params.Big.poly_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T15:31:15.403378+00:00
-- url     : https://prove2.me/theorems/2c5a8e4a-5d1d-44f3-a1df-b4eabb3d5531
-- title:
--   Big: poly le
-- statement:
--   12·Δ·⌈log₂(2Δ)⌉·ℓ ≤ 2^{⌊ℓ/2⌋}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L421-L430
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L421-L430

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

theorem ClauseBound.ParityChecks.Params.Big.poly_le : 12 * Δ * LD Δ * ℓ ≤ 2 ^ (ℓ / 2) := by sorry
