-- Prove2me | Theorems.Thm_ClauseBound_Part_Lower_sum_k_ge
-- name    : ClauseBound.Part.Lower.sum_k_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:02:54.9676+00:00
-- url     : https://prove2.me/theorems/14363287-05a6-45aa-a5b2-27c66a6e1464
-- title:
--   Lower: sum k ge
-- statement:
--   The sum over 1 ≤ k ≤ K of the lower bounds for the sums over v.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L254-L269
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/rates/ClauseBound/Part/Lower.lean#L254-L269

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

theorem ClauseBound.Part.Lower.sum_k_ge {α γ : ℝ} (hα : 0 < α) (hγ : 0 ≤ γ) {K : ℕ} (hK : 1 ≤ K) :
    1 / α ^ 2 * (Real.pi ^ 2 / 6 - 1 / K) - K / 4 - 486 * γ / α ^ 4 * (Real.pi ^ 2 / 6)
      ≤ ∑ k ∈ Ioc 0 K, (1 / (α * k) ^ 2 - 1 / 4 - 486 * (γ * (k : ℝ) ^ 2) / (α * k) ^ 4) := by sorry
