-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_initList_self
-- name    : CircuitLowerBound.Oracle.initList_self
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:46:08.737502+00:00
-- url     : https://prove2.me/theorems/9878c6a1-ddd7-41cf-b70c-ecbc653f1152
-- title:
--   Oracle: init List self
-- statement:
--   The Oracle construction uses the init List self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L33-L33
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L33-L33

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

theorem CircuitLowerBound.Oracle.initList_self (tm : FinTM2) (s : List (tm.Γ tm.k₀)) : (initList tm s).stk tm.k₀ = s := by sorry
