-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_liftCfg_init
-- name    : CircuitLowerBound.Oracle.liftCfg_init
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:45:56.003712+00:00
-- url     : https://prove2.me/theorems/8e6f4e14-7415-46ed-99a4-4a1239a5f3d3
-- title:
--   Oracle: lift Cfg init
-- statement:
--   The Oracle construction uses the lift Cfg init property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L157-L161
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Runs.lean#L157-L161

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

theorem CircuitLowerBound.Oracle.liftCfg_init (n : NS → List Bool) (s : List (M.tm.Γ M.tm.k₀)) :
    liftCfg n (initList M.tm s) = ⟨some (.inl M.tm.main), (M.tm.initialState, none), stk M (one M.tm.k₀ s) n⟩ := by sorry
