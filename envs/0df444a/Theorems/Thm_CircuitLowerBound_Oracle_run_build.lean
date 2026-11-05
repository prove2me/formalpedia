-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_run_build
-- name    : CircuitLowerBound.Oracle.run_build
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:44:28.050765+00:00
-- url     : https://prove2.me/theorems/c0313e4e-883d-4273-b9dc-81c470e55f99
-- title:
--   Oracle: run build
-- statement:
--   Before M runs: the input of the round is written on the input stack of M; x and the answers are
--   kept.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L134-L155
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L134-L155

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

theorem CircuitLowerBound.Oracle.run_build (v : M.tm.σ) (x ans : List Bool) :
    Run (stp M O) ⟨some (.inr .cpA), (v, none), stk M (one M.tm.k₀ []) (ns x ans.reverse [])⟩ (2 * ans.length + 2 * x.length + 5)
      ⟨some (.inl M.tm.main), (v, none), stk M (one M.tm.k₀ ((roundInput x ans).map M.inputAlphabet.invFun)) (ns x ans.reverse [])⟩ := by sorry
