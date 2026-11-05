-- Prove2me | Theorems.Thm_CircuitLowerBound_Time_final_le
-- name    : CircuitLowerBound.Time.final_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:09:46.423296+00:00
-- url     : https://prove2.me/theorems/12658379-6768-43e6-9e5a-d04dcea533a7
-- title:
--   Time: final le
-- statement:
--   K·2^{m/32}·2^{m/32} ≤ 2^{⌊m/8⌋} for m ≥ 16(K + 1).
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Time.lean#L33-L48
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Alg/Time.lean#L33-L48

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

theorem CircuitLowerBound.Time.final_le (K : ℕ) {m : ℕ} (hm : 16 * (K + 1) ≤ m) :
    (K : ℝ) * ((2 : ℝ) ^ ((1 / 32 : ℝ) * m) * (2 : ℝ) ^ ((1 / 32 : ℝ) * m)) ≤ (2 : ℝ) ^ (((m / 8 : ℕ) : ℝ)) := by sorry
