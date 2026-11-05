-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_run_round
-- name    : CircuitLowerBound.Oracle.run_round
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:46:30.764599+00:00
-- url     : https://prove2.me/theorems/d0a46564-23c7-41e9-98a5-70ab2e04f13a
-- title:
--   Oracle: run round
-- statement:
--   A whole round up to the step after M's run: the first bit c of the output of M is gone and has
--   decided where the machine goes on.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L171-L188
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L171-L188

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

theorem CircuitLowerBound.Oracle.run_round {T : ℕ} {x ans : List Bool} {c : Bool} {w : List Bool} (h : Round M T x ans (c :: w)) :
    ∃ t ≤ 2 * ans.length + 2 * x.length + T + 6,
      Run (stp M O) ⟨some (.inr .cpA), (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns x ans.reverse [])⟩ t
        ⟨some (if c then .inr .ask else .inr .drX), (M.tm.initialState, none),
          stk M (one M.tm.k₁ (w.map M.outputAlphabet.invFun)) (ns x ans.reverse [])⟩ := by sorry
