-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_haltList_ne
-- name    : CircuitLowerBound.Oracle.haltList_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:46:25.468601+00:00
-- url     : https://prove2.me/theorems/8ffb882d-2c26-43bc-bbc8-79189711a5e2
-- title:
--   Oracle: halt List ne
-- statement:
--   The Oracle construction uses the halt List ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L39-L39
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L39-L39

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

theorem CircuitLowerBound.Oracle.haltList_ne (tm : FinTM2) (s : List (tm.Γ tm.k₁)) {k : tm.K} (h : k ≠ tm.k₁) : (haltList tm s).stk k = [] := by sorry
