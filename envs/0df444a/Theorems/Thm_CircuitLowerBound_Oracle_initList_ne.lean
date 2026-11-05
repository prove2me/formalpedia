-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_initList_ne
-- name    : CircuitLowerBound.Oracle.initList_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-04T18:46:17.88385+00:00
-- url     : https://prove2.me/theorems/6d4c90bf-39f8-4188-95d5-e3a8287f17f1
-- title:
--   Oracle: init List ne
-- statement:
--   The Oracle construction uses the init List ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L35-L35
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L35-L35

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

theorem CircuitLowerBound.Oracle.initList_ne (tm : FinTM2) (s : List (tm.Γ tm.k₀)) {k : tm.K} (h : k ≠ tm.k₀) : (initList tm s).stk k = [] := by sorry
