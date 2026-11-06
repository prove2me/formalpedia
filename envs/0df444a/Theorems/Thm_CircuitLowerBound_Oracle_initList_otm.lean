-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_initList_otm
-- name    : CircuitLowerBound.Oracle.initList_otm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:46:27.882972+00:00
-- url     : https://prove2.me/theorems/dc0003ca-00e3-4baa-9292-96156609564e
-- title:
--   Oracle: init List otm
-- statement:
--   The first configuration of the oracle machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L42-L53
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L42-L53

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_Oracle_Runs
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Restart
import Theorems.Thm_Groundwork_TM_Run_one

set_option autoImplicit false
section
section
open CircuitLowerBound
open ENP Turing Groundwork.TM
open CircuitLowerBound.Oracle
variable {M : TM2ComputableAux Bool Bool}

theorem CircuitLowerBound.Oracle.initList_otm (x : List Bool) :
    initList (otm M).tm (x.map (otm M).inp.symm) = (⟨some (.inr .cpA), (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns x [] [])⟩ : Cf M) := by sorry
