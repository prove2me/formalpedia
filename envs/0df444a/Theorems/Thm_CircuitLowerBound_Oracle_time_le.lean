-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_time_le
-- name    : CircuitLowerBound.Oracle.time_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:47:06.584288+00:00
-- url     : https://prove2.me/theorems/9f050822-498c-48bd-aeea-098924644964
-- title:
--   Oracle: time le
-- statement:
--   The time: (Y + 1)·(4Y + 3n + 12) ≤ 2^{(2c+7)(n+1)} for Y = 2^{c(n+1)}.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L70-L88
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L70-L88

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Restart
set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Turing Groundwork.TM
open CircuitLowerBound.Oracle
variable {M : TM2ComputableAux Bool Bool}

theorem CircuitLowerBound.Oracle.time_le (c n : ℕ) :
    (2 ^ (c * (n + 1)) + 1) * (3 * (0 + 2 ^ (c * (n + 1))) + 3 * n + 2 ^ (c * (n + 1)) + 12) ≤ 2 ^ ((2 * c + 7) * (n + 1)) := by sorry
