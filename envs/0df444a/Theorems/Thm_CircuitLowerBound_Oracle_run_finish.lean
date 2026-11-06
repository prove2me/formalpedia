-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_run_finish
-- name    : CircuitLowerBound.Oracle.run_finish
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:45:58.92983+00:00
-- url     : https://prove2.me/theorems/80345b29-c794-49cf-88d7-542768a95206
-- title:
--   Oracle: run finish
-- statement:
--   The end: x and the answers are dropped, the result goes to the output stack.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L191-L207
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L191-L207

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

theorem CircuitLowerBound.Oracle.run_finish (x ans : List Bool) (b : Bool) :
    Run (stp M O) ⟨some (.inr .drX), (M.tm.initialState, none), stk M (one M.tm.k₁ ([b].map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩
      (x.length + ans.length + 3) ⟨none, (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns [b] [] [])⟩ := by sorry
