-- Prove2me | Theorems.Thm_ClauseBound_ParityChecks_Params_series_real
-- name    : ClauseBound.ParityChecks.Params.series_real
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T16:25:49.8422+00:00
-- url     : https://prove2.me/theorems/f514add9-961f-4753-a56d-ca7fb6399701
-- title:
--   Params: series real
-- statement:
--   The binomial series cut off at i₀, over the real numbers.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L379-L413
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/ParityChecks/Params.lean#L379-L413

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

theorem ClauseBound.ParityChecks.Params.series_real {u nb i₀ m h : ℕ} (hu : u ≤ m) (hi0 : 1 ≤ i₀) (hnb : 1 ≤ nb) (hh : 1 ≤ h) (key : 6 * m * 2 ^ h ≤ nb * i₀) :
    |(1 - 2 * (1 / (nb : ℝ))) ^ u - ∑ i ∈ range (i₀ + 1), (-2 * (1 / (nb : ℝ))) ^ i * (u.choose i : ℝ)| ≤ 2 * (1 / 2 ^ h) ^ i₀ := by sorry
