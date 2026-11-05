-- Prove2me | Theorems.Thm_CircuitLowerBound_Time_exists_threshold
-- name    : CircuitLowerBound.Time.exists_threshold
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:09:30.557332+00:00
-- url     : https://prove2.me/theorems/050150ab-ecc4-47e7-83b9-24358c9bbd87
-- title:
--   Time: exists threshold
-- statement:
--   The threshold.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Time.lean#L69-L118
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Time.lean#L69-L118

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Alg_Machine
import Definitions.Def_ToTuring_Machine_EndTM
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Alg_Time
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork Turing
open CircuitLowerBound.Time

theorem CircuitLowerBound.Time.exists_threshold (q cE c₀ a₀ G : ℕ) : ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → ∀ n Nv T : ℕ, n ≤ c₀ * (m + 1) → Nv ≤ 3 * n + a₀ * (m + 1) + G →
    (T : ℝ) ≤ cE * (2 : ℝ) ^ (1 / (32 * ((3 * c₀ + a₀ + 1 : ℕ) : ℝ)) * Nv) →
    q * (T + 1) * ((m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + cE * (Nv + 2) ^ cE + 1) ^ q ≤ 2 ^ (m / 8) := by sorry
