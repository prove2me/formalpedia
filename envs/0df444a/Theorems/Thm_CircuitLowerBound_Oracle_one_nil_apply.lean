-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_one_nil_apply
-- name    : CircuitLowerBound.Oracle.one_nil_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:52.806231+00:00
-- url     : https://prove2.me/theorems/ab374c60-941a-40b6-a430-8e11a953bba8
-- title:
--   Oracle: one nil apply
-- statement:
--   The Oracle construction uses the one nil apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L28-L31
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Restart.lean#L28-L31

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

theorem CircuitLowerBound.Oracle.one_nil_apply (k k' : M.tm.K) : (one k [] : ∀ k', List (M.tm.Γ k')) k' = [] := by sorry
