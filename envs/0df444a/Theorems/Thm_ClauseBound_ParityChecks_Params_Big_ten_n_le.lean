-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_ten_n_le
-- name    : ClauseBound.ParityChecks.Params.Big.ten_n_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:50.492421+00:00
-- url     : https://prove2.me/theorems/374fd638-3869-472c-8e20-dc723e02c487
-- title:
--   Big: ten n le
-- statement:
--   10n ≤ ⌈ℓ/2⌉·i₀.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L450-L454
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L450-L454

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

theorem ClauseBound.ParityChecks.Params.Big.ten_n_le : 10 * n ≤ (ℓ - ℓ / 2) * i0Of n := by sorry
