-- Prove2me | Theorems.Thm_CircuitLowerBound_Oracle_update_inl
-- name    : CircuitLowerBound.Oracle.update_inl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T17:58:03.27297+00:00
-- url     : https://prove2.me/theorems/e977bd44-53e0-41ab-8c80-b604679cbf6d
-- title:
--   Oracle: update inl
-- statement:
--   The Oracle construction uses the update inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L168-L175
-- source:
--   https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/proof/consequences/CircuitLowerBound/Oracle/Machine.lean#L168-L175

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_CircuitLowerBound_InterfacesPolyT
import Definitions.Def_ToTuring_TM_Run
import Mathlib.Tactic
import Definitions.Def_CircuitLowerBound_Oracle_Machine
set_option autoImplicit false
section
section
open CircuitLowerBound CircuitLowerBound.Oracle
open ENP Turing Groundwork.TM
variable (M : TM2ComputableAux Bool Bool)
variable {M}

theorem CircuitLowerBound.Oracle.update_inl (T : ∀ k, List (M.tm.Γ k)) (n : NS → List Bool) (k : M.tm.K) (w : List (M.tm.Γ k)) :
    Function.update (stk M T n) (.inl k) w = stk M (Function.update T k w) n := by sorry
