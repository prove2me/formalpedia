-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_run_protocol
-- name    : CircuitLowerBound.Oracle.run_protocol
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:46:03.147242+00:00
-- url     : https://prove2.me/theorems/fa9d51ea-23f2-40f7-adc8-a40c02705e16
-- title:
--   Oracle: run protocol
-- statement:
--   The whole run, from a point between two rounds.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L228-L248
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L228-L248

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Theorems.Thm_Groundwork_TM_Run_one

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable {M : TM2ComputableAux Bool Bool} (O : Lang)

theorem CircuitLowerBound.Oracle.run_protocol {T : ℕ} {x : List Bool} {b : Bool} {ans : List Bool} {r : ℕ} (h : Protocol M T x b ans r) :
    ∃ t ≤ (r + 1) * (3 * (ans.length + r) + 3 * x.length + T + 12),
      Run (stp M SAT) ⟨some (.inr .cpA), (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns x ans.reverse [])⟩ t
        ⟨none, (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns [b] [] [])⟩ := by sorry
