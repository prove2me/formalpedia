-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_Big_series
-- name    : ClauseBound.ParityChecks.Params.Big.series
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:49.650196+00:00
-- url     : https://prove2.me/theorems/7a5fc3b6-f52b-4bb4-88f4-749d8f7b1279
-- title:
--   Big: series
-- statement:
--   The binomial series cut off at i₀.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L457-L470
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L457-L470

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

theorem ClauseBound.ParityChecks.Params.Big.series (u : ℕ) (hu : u ≤ m) :
    |(1 - 2 * pr (nbOf n Δ)) ^ u - ∑ i ∈ range (i0Of n + 1), (-2 * pr (nbOf n Δ)) ^ i * (u.choose i : ℚ)| ≤ 2 / 2 ^ (10 * n) := by sorry
