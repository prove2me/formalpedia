-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_run_query
-- name    : CircuitLowerBound.Oracle.run_query
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:46:10.708327+00:00
-- url     : https://prove2.me/theorems/a2c2335e-2aa5-4084-98d3-edf5b96d45ee
-- title:
--   Oracle: run query
-- statement:
--   A query and its answer: two steps.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L211-L225
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L211-L225

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
open Classical

theorem CircuitLowerBound.Oracle.run_query (x ans w : List Bool) :
    Run (stp M O) ⟨some (.inr .ask), (M.tm.initialState, none), stk M (one M.tm.k₁ (w.map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩ 2
      ⟨some (.inr .cpA), (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns x (ans ++ [decide (O w)]).reverse [])⟩ := by sorry
