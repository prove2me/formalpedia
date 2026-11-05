-- Prove2me | Theorems.Thm_CircuitLowerBound_Time_base_le
-- name    : CircuitLowerBound.Time.base_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:09:27.037704+00:00
-- url     : https://prove2.me/theorems/d1c3dd40-1f70-4f64-8ee6-7db0685084cd
-- title:
--   Time: base le
-- statement:
--   The length of the input and the size of the states are polynomial in m. Here n is the number of
--   gates and Nv the number of variables.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Time.lean#L52-L66
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Time.lean#L52-L66

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

theorem CircuitLowerBound.Time.base_le {cE c₀ a₀ G m n Nv : ℕ} (hn : n ≤ c₀ * (m + 1)) (hNv : Nv ≤ 3 * n + a₀ * (m + 1) + G) :
    (m + 1 + ((m + n) + 1 + n * (4 + 2 * (m + n)))) + cE * (Nv + 2) ^ cE + 1
      ≤ (8 + cE) * (3 * c₀ + a₀ + G + 2) ^ (cE + 2) * (m + 2) ^ (cE + 2) := by sorry
