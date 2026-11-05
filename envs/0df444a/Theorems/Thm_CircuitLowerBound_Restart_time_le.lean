-- Prove2me | Theorems.Thm_CircuitLowerBound_Restart_time_le
-- name    : CircuitLowerBound.Restart.time_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-05T04:09:20.823205+00:00
-- url     : https://prove2.me/theorems/44d17442-2d50-4393-8eca-5dd77cb02518
-- title:
--   Restart: time le
-- statement:
--   The time of a round on x and a ≤ 2^m answers, m = |x|.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Restart.lean#L43-L54
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/ENP/Restart.lean#L43-L54

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_ENP_Round
import Definitions.Def_CircuitLowerBound_Small
import Definitions.Def_CountKSatRate_Pad
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_ENP_Restart
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Groundwork PaddedDescent Turing
open CircuitLowerBound.Restart

theorem CircuitLowerBound.Restart.time_le (q m a : ℕ) (ha : a ≤ 2 ^ m) : q * (2 * m + 1 + a + 2 ^ (2 * m + 4) + 1) ^ q ≤ 2 ^ ((6 * q + 1) * (m + 1)) := by sorry
