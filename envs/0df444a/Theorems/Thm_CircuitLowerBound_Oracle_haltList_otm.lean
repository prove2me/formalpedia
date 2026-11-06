-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_haltList_otm
-- name    : CircuitLowerBound.Oracle.haltList_otm
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:46:42.384075+00:00
-- url     : https://prove2.me/theorems/3c21ba63-2bf5-4683-8e37-1eb19c927c1d
-- title:
--   Oracle: halt List otm
-- statement:
--   The last configuration of the oracle machine.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L56-L67
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L56-L67

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

theorem CircuitLowerBound.Oracle.haltList_otm (b : Bool) :
    haltList (otm M).tm [(otm M).out.symm b] = (⟨none, (M.tm.initialState, none), stk M (one M.tm.k₀ []) (ns [b] [] [])⟩ : Cf M) := by sorry
