-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_one_nil
-- name    : CircuitLowerBound.Oracle.one_nil
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T18:39:37.723747+00:00
-- url     : https://prove2.me/theorems/3a45d0af-24e0-48d7-8b85-46a538ffd8f0
-- title:
--   Oracle: one nil
-- statement:
--   The Oracle construction uses the one nil property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L209-L212
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L209-L212

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_TM_Run
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Machine
import Theorems.Thm_Groundwork_TM_Run_one

set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable (M : TM2ComputableAux Bool Bool)
variable {M}

theorem CircuitLowerBound.Oracle.one_nil (k k' : M.tm.K) : (one k [] : ∀ k', List (M.tm.Γ k')) = one k' [] := by sorry
