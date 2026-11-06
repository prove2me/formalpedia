-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_liftCfg_halt
-- name    : CircuitLowerBound.Oracle.liftCfg_halt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:45:52.185207+00:00
-- url     : https://prove2.me/theorems/eb740a41-f6c4-4cea-84af-0996d1f085e0
-- title:
--   Oracle: lift Cfg halt
-- statement:
--   The Oracle construction uses the lift Cfg halt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L163-L167
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L163-L167

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

theorem CircuitLowerBound.Oracle.liftCfg_halt (n : NS → List Bool) (s : List (M.tm.Γ M.tm.k₁)) :
    liftCfg n (haltList M.tm s) = ⟨some (.inr .after), (M.tm.initialState, none), stk M (one M.tm.k₁ s) n⟩ := by sorry
