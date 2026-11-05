-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_le_sum_inv_sq
-- name    : ClauseBound.Part.Lower.le_sum_inv_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:50.080971+00:00
-- url     : https://prove2.me/theorems/2923d930-f0a7-4c31-9358-d0066068191c
-- title:
--   Lower: le sum inv sq
-- statement:
--   Σ_{k ≤ K} 1/k² ≥ π²/6 − 1/K.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L232-L251
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L232-L251

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_ClauseBound_Part_Rec
import Definitions.Def_ClauseBound_Part_Lower
set_option autoImplicit false
section
section
open ClauseBound ClauseBound.Part
open Finset Partitions
open ClauseBound.Part.Lower

theorem ClauseBound.Part.Lower.le_sum_inv_sq {K : ℕ} (hK : 1 ≤ K) : Real.pi ^ 2 / 6 - 1 / K ≤ ∑ k ∈ Ioc 0 K, 1 / (k : ℝ) ^ 2 := by sorry
